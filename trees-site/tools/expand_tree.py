#!/usr/bin/env python3
"""Write the full tree of a compiled circuit from the page's plan.

Input: the "Plan (.json)" downloaded from the circuit compiler. Output: every
vertex and edge of the tree of the degree-5 reduction (macrocells, leaves,
constant cherries, one generator per control, the EVER receiver), as text:

    # comments
    n <vertices>
    states <one 0/1 character per vertex, vertex 0 first>
    query <vertex> <time>          (a main vertex of the output register at T)
    ever <vertex>                  (only with the receiver z)
    <u> <v>                        (one line per edge)

Vertices take the majority of their neighbours and keep their state on a tie;
all degrees are 1, 3 or 5. With --check, the tree is also simulated directly
with tools/generator/majsim.c, and the output register at T and z are compared
with the circuit. The trees are large (tens of millions of vertices already for
two nodes); --max-vertices guards against accidents.
"""
import argparse
import json
import os
import struct
import subprocess
import sys
import tempfile
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))


def bit_length(x):
    return x.bit_length()


class History:
    """Initial bit and sorted change times (the port history of a control)."""

    def __init__(self, b0, ch):
        self.b0, self.ch = int(b0), list(ch)

    def q(self, t):
        lo, hi = 0, len(self.ch)
        while lo < hi:
            mid = (lo + hi) // 2
            if self.ch[mid] <= t:
                lo = mid + 1
            else:
                hi = mid
        return lo

    def at(self, t):
        return self.b0 ^ (self.q(t) & 1)

    def child(self, j):
        b0 = self.at(1) ^ int(self.q(1) % 4 == j)
        ch = [c - 1 for a, c in enumerate(self.ch, 1) if c >= 2 and j not in ((a - 1) % 4, a % 4)]
        return History(b0, ch)


class Writer:
    def __init__(self, out, limit):
        self.out, self.limit = out, limit
        self.states = bytearray()
        self.au, self.av = array('i'), array('i')

    def add(self, s):
        if len(self.states) >= self.limit:
            raise SystemExit('the tree exceeds --max-vertices (%d)' % self.limit)
        self.states.append(48 + (1 if s else 0))
        return len(self.states) - 1

    def link(self, u, v):
        self.au.append(u); self.av.append(v)

    # hardness.txt section 2 and 3; degree-review.txt sections 1 and 2
    def cherry(self, b):
        a = self.add(b)
        self.link(a, self.add(b)); self.link(a, self.add(b))
        return a

    def timer(self, tau, rising):
        if tau < 1:
            raise ValueError('timer date %d' % tau)
        arm, cb = (0, 1) if rising else (1, 0)
        r = self.add(arm)
        for _ in range(2):
            prev = r
            for _ in range(tau - 1):
                v = self.add(arm)
                self.link(prev, v)
                self.link(v, self.cherry(cb))
                prev = v
            self.link(prev, self.cherry(cb))
        return r

    def pulse(self, a, b, neg):
        top = prev = None
        for level in range(a):
            aa, bb = a - level, b - level
            r = self.add(1 if neg else 0)
            if prev is None:
                top = r
            else:
                self.link(prev, r)
            self.link(r, self.timer(bb - 1, neg))
            if aa == 1:
                self.link(r, self.timer(bb - 1, neg))
            self.link(r, self.cherry(1 if neg else 0))
            self.link(r, self.cherry(0 if neg else 1) if aa == 1 else self.timer(aa - 1, not neg))
            prev = r
        return top

    def generator(self, h):
        K = len(h.ch)
        if K == 0:
            return self.cherry(h.b0)
        if K == 1:
            return self.timer(h.ch[0], h.b0 == 0)
        if K == 2:
            return self.pulse(h.ch[0], h.ch[1], h.b0 == 1)
        r = self.add(h.b0)
        for j in range(4):
            self.link(r, self.generator(h.child(j)))
        return r


def expand(plan, limit):
    if plan.get('format') != 'majority-trees-plan/1':
        raise SystemExit('not a plan from the Majority on trees compiler')
    w = Writer(None, limit)
    cell = {}
    for c in plan['cells']:
        b = c['initial']
        v = {X: w.add(b) for X in ('A', 'C', 'B', 'a', 'b')}
        w.link(v['A'], v['C']); w.link(v['C'], v['B']); w.link(v['A'], v['a']); w.link(v['B'], v['b'])
        cell[c['name']] = v
    for c in plan['controls']:
        port = w.generator(History(c['initial'], c['changes']))
        w.link(cell[c['cell']][c['vertex']], port)
    for p in plan['ports']:
        (a, X), (b, Y) = p['from'].split('.'), p['to'].split('.')
        w.link(cell[a][X], cell[b][Y])
    for name in plan['constantPorts']:
        a, X = name.split('.')
        w.link(cell[a][X], w.cherry(0))
    z = None
    if plan.get('receiver'):
        a, X = plan['receiver']['attachedTo'].split('.')
        z = w.add(0)
        w.link(z, w.add(0))
        w.link(cell[a][X], z)
        w.link(z, w.timer(plan['receiver']['timerDate'], True))
    out = cell['r%d' % plan['M']]
    return w, out, z


def circuit_value(plan):
    val = []
    for i, nd in enumerate(plan['circuit']['nodes']):
        if nd['kind'] == 'const':
            val.append(plan['circuit']['inputBits'][i])
        else:
            a, b = val[nd['p'] - 1], val[nd['q'] - 1]
            val.append(a & b if nd['kind'] == 'and' else a | b)
    return val[-1]


def check(w, out, z, plan, build):
    """Direct simulation with majsim (explicit tree, every weight 1)."""
    src = os.path.join(HERE, 'generator', 'majsim.c')
    os.makedirs(build, exist_ok=True)
    exe = os.path.join(build, 'majsim')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-fopenmp', '-o', exe, src], check=True)
    T = plan['T']
    Tmax = T + 6
    probes = [out['A'], out['C'], out['B']] + ([z] if z is not None else [])
    n, E = len(w.states), len(w.au)
    with tempfile.TemporaryDirectory(dir=build) as d:
        inp, res = os.path.join(d, 'in.bin'), os.path.join(d, 'out.bin')
        with open(inp, 'wb') as f:
            f.write(b'MAJ2'); f.write(struct.pack('<i', 0))
            f.write(struct.pack('<8q', n, 2 * E, 0, 0, len(probes), 1, 0, Tmax))
            f.write(bytes(c - 48 for c in w.states))
            # arcs in pairs, (a, b) then (b, a); written in blocks to save memory
            for first, second in ((w.au, w.av), (w.av, w.au)):
                for k in range(0, E, 1 << 20):
                    a, b = first[k:k + (1 << 20)], second[k:k + (1 << 20)]
                    block = array('i', bytes(8 * len(a)))
                    block[0::2] = a; block[1::2] = b
                    block.tofile(f)
            f.write(b'\x01' * (2 * E))
            array('i', probes).tofile(f)
        w.au = w.av = w.states = None        # free the tree before the simulation
        info = subprocess.run([exe, inp, res], capture_output=True, text=True, check=True)
        data = open(res, 'rb').read()
    stats = json.loads(info.stdout)
    W = Tmax + 1
    hist = [data[i * W:(i + 1) * W] for i in range(len(probes))]
    want = circuit_value(plan)
    ok = all(h[T] == want for h in hist[:3])
    msg = ['output register at T: %s (circuit: %d)' % ([h[T] for h in hist[:3]], want)]
    if z is not None:
        zok = not any(hist[3][:T + 2]) and (1 in hist[3]) == bool(want)
        ok = ok and zok
        msg.append('z: 0 until T+1, ever 1 = %s' % (1 in hist[3]))
    good_tree = stats['cycles'] == 0 and stats['components'] == 1 and stats['maxdeg'] <= 5 and stats['even_degree'] == 0
    msg.append('tree: %d vertices, %s, max degree %d, even degrees %d' % (
        stats['n'], 'connected and acyclic' if good_tree else 'NOT A TREE', stats['maxdeg'], stats['even_degree']))
    return ok and good_tree, msg


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('plan', help='plan downloaded from the compiler')
    ap.add_argument('-o', '--out', help='output file (default: <plan>-tree.txt)')
    ap.add_argument('--max-vertices', type=int, default=60_000_000)
    ap.add_argument('--check', action='store_true', help='simulate the tree and compare with the circuit')
    ap.add_argument('--no-write', action='store_true', help='with --check: do not write the edge list')
    ap.add_argument('--build', default=os.path.join(tempfile.gettempdir(), 'trees-site-build'))
    args = ap.parse_args()
    with open(args.plan) as f:
        plan = json.load(f)
    w, out, z = expand(plan, args.max_vertices)
    print('%d vertices, %d edges' % (len(w.states), len(w.au)))
    if not args.no_write:
        path = args.out or os.path.splitext(args.plan)[0] + '-tree.txt'
        with open(path, 'w') as f:
            f.write('# Majority on trees: full tree of the degree-5 reduction (from %s)\n' % os.path.basename(args.plan))
            f.write('# Rule: synchronous majority of neighbours, ties keep the state; degrees 1, 3, 5.\n')
            f.write('n %d\nstates ' % len(w.states))
            f.write(w.states.decode())
            f.write('\nquery %d %d\n' % (out['A'], plan['T']))
            if z is not None:
                f.write('ever %d\n' % z)
            for u, v in zip(w.au, w.av):
                f.write('%d %d\n' % (u, v))
        print('wrote', path)
    if args.check:
        ok, msg = check(w, out, z, plan, args.build)
        print('\n'.join(msg))
        print('CHECK PASSED' if ok else 'CHECK FAILED')
        return 0 if ok else 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
