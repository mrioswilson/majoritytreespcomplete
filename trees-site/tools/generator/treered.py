#!/usr/bin/env python3
"""Adversarial check of the tree reduction in
research/majority-treewidth-deepen-20261006 by direct simulation.

The construction is re-implemented here from the text of the notes:
  hardness.txt        generator G: cherries, two-arm timers, robust AND/OR,
                      bases with at most four changes, four-child recursion
                      with a rotating dissident, common prefix S;
  tree-algorithm.txt  memory cells with four leaves and q+5 private
                      generators, bus skeleton, serial MCVP program;
  root-analysis.txt   H, S, T and the EVER receiver.
majsim.c runs plain synchronous majority (ties keep the state) on the tree.

Encodings.  compress=False writes every vertex and edge of the tree.
compress=True stores k identical private subtrees hanging from the same
vertex once, with multiplicity k.  This is exact: the copies start equal and
their only outside neighbour is the common parent, so they stay equal.  The
suite runs both encodings on the same instances to cross-check them, and a
pure-Python simulator cross-checks majsim on small instances.
"""
import argparse
import bisect
import itertools
import json
import os
import random
import struct
import subprocess
import sys
import tempfile
import time
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD, RESET, EVAL1, EVAL2 = 'HOLD', 'RESET', 'EVAL1', 'EVAL2'
MUT = set()   # deliberate defects, used only by test_mutations


def S_of(H):
    """S = ceil(log2(H+2)) + 8 (hardness.txt, Theorem G)."""
    return (H + 1).bit_length() + 8


class Hist:
    """Binary history on t >= 0: initial bit and sorted change times (>= 1)."""
    __slots__ = ('b0', 'ch')

    def __init__(self, b0, ch):
        self.b0, self.ch = int(b0), tuple(ch)

    @property
    def K(self):
        return len(self.ch)

    def q(self, t):
        return bisect.bisect_right(self.ch, t)

    def at(self, t):
        return self.b0 ^ (self.q(t) & 1)

    def child(self, j):
        """(G3): h_j(t) = h(t+1) xor [j = q(t+1) mod 4]."""
        if 'child_no_shift' in MUT:
            return Hist(self.b0 ^ int(j == 0), [c for a, c in enumerate(self.ch, 1)
                                                if j not in ((a - 1) % 4, a % 4)])
        b0 = self.at(1) ^ int(self.q(1) % 4 == j)
        ch = [c - 1 for a, c in enumerate(self.ch, 1)
              if c >= 2 and j not in ((a - 1) % 4, a % 4)]
        return Hist(b0, ch)

    def intervals(self):
        pts = (0,) + self.ch
        return [(a, pts[k + 1] if k + 1 < len(pts) else None)
                for k, a in enumerate(pts) if self.b0 ^ (k & 1)]


def word_hist(w):
    """Root target of (G1): w(0) before S, then w(min(t-S, H))."""
    H = len(w) - 1
    S = S_of(H)
    return Hist(w[0], [S + t for t in range(1, H + 1) if w[t] != w[t - 1]])


def word_expected(w, Tmax):
    H = len(w) - 1
    S = S_of(H)
    return [w[0] if t < S else w[min(t - S, H)] for t in range(Tmax + 1)]


def g_closed(j, q):
    """(G4): changes of child j after q changes of its parent."""
    return 2 * (q // 4) + sum(j not in ((a - 1) % 4, a % 4) for a in range(1, q % 4 + 1))


# ---------------------------------------------------------------- the tree

class Net:
    def __init__(self, compress=True):
        self.compress = compress
        self.state = array('B')
        self.au, self.av, self.aw = array('i'), array('i'), array('B')
        self.timers = array('i')
        self.extra = 0
        self.forced = []
        self.stats = dict(timers=0, min_timer=None, max_timer=0, max_depth=0, leaves=0,
                          max_leaf_K=0, min_leaf_change=None, gates=0, nodes=0)

    def n(self):
        return len(self.state) + self.extra

    def add(self, s):
        self.state.append(s)
        return len(self.state) - 1

    def link(self, p, c, k=1):
        """p counts c k times, c counts p once (k > 1 only when compressing)."""
        self.au.append(p); self.av.append(c); self.aw.append(k)
        self.au.append(c); self.av.append(p); self.aw.append(1)

    def hang(self, parent, k, build):
        """k private identical copies of build() hanging from parent.
        Returns (ports, initial state of a port, size of the plain tree)."""
        if self.compress:
            port, init, size = build()
            self.link(parent, port, k)
            return [port], init, k * size
        ports, total, init = [], 0, None
        for _ in range(k):
            port, init, size = build()
            self.link(parent, port, 1)
            ports.append(port)
            total += size
        return ports, init, total

    def leaf(self, b):
        return self.add(b), b, 1

    def cherry(self, b):
        """hardness.txt section 2: root and two leaves, all b."""
        a = self.add(b)
        _, _, s = self.hang(a, 2, lambda: self.leaf(b))
        return a, b, 1 + s

    def timer(self, tau, rising):
        """hardness.txt section 3 (expanded by majsim / ref_sim)."""
        if tau < 1:
            raise ValueError('timer date %d < 1' % tau)
        r = self.add(0 if rising else 1)
        self.timers.extend((r, tau, 1 if rising else 0))
        L = tau - 1
        self.extra += 3 * L + 2 if self.compress else 8 * L + 6
        s = self.stats
        s['timers'] += 1
        s['min_timer'] = tau if s['min_timer'] is None else min(s['min_timer'], tau)
        s['max_timer'] = max(s['max_timer'], tau)
        return r, (0 if rising else 1), 8 * tau - 1

    def formula(self, node, ell):
        """Section 4: gate with two private copies of each input, two
        constants and the parent; timers advanced by their gate distance."""
        kind = node[0]
        if kind == 'C':
            return self.cherry(node[1])
        adv = 0 if 'no_advance' in MUT else ell
        if kind == 'UP':
            return self.timer(node[1] - adv, True)
        if kind == 'DOWN':
            return self.timer(node[1] - adv, False)
        op, X, Y = node
        g = self.add(0)
        self.stats['gates'] += 1
        kc = 1 if 'single_copy' in MUT else 2
        _, ix, sx = self.hang(g, kc, lambda: self.formula(X, ell + 1))
        _, iy, sy = self.hang(g, kc, lambda: self.formula(Y, ell + 1))
        cb = 0 if op == 'AND' else 1
        _, _, sc = self.hang(g, 2, lambda: self.cherry(cb))
        init = ix & iy if op == 'AND' else ix | iy
        self.state[g] = init
        return g, init, 1 + sx + sy + sc

    def base(self, h):
        """Section 5: OR of <= 3 intervals U_a AND D_b."""
        if h.K == 0:
            return self.cherry(h.b0)
        I = [('AND', ('C', 1) if a == 0 else ('UP', a), ('C', 1) if b is None else ('DOWN', b))
             for a, b in h.intervals()]
        assert 1 <= len(I) <= 3, I
        F = I[0] if len(I) == 1 else ('OR', I[0], I[1]) if len(I) == 2 else ('OR', ('OR', I[0], I[1]), I[2])
        return self.formula(F, 0)

    def generator(self, h, depth=0):
        """Section 6: recursion on the number of changes."""
        s = self.stats
        s['max_depth'] = max(s['max_depth'], depth)
        if h.K <= 4:
            s['leaves'] += 1
            s['max_leaf_K'] = max(s['max_leaf_K'], h.K)
            if h.K:
                m = s['min_leaf_change']
                s['min_leaf_change'] = h.ch[0] if m is None else min(m, h.ch[0])
            return self.base(h)
        r = self.add(h.b0)
        s['nodes'] += 1
        size = 1
        for j in range(4):
            _, _, sz = self.hang(r, 1, lambda c=h.child(j): self.generator(c, depth + 1))
            size += sz
        return r, h.b0, size

    def dump(self, path, Tmax, probes, ov_vertices=(), ov_sets=((),)):
        with open(path, 'wb') as f:
            f.write(b'MAJ2')
            f.write(struct.pack('<i', 1 if self.compress else 0))
            f.write(struct.pack('<8q', len(self.state), len(self.au), len(self.timers) // 3,
                                len(self.forced), len(probes), len(ov_sets), len(ov_vertices), Tmax))
            self.state.tofile(f)
            self.timers.tofile(f)
            self.au.tofile(f); self.av.tofile(f); self.aw.tofile(f)
            array('i', [v for v, _ in self.forced]).tofile(f)
            for _, bits in self.forced:
                assert len(bits) == Tmax + 1
                f.write(bytes(bits))
            array('i', probes).tofile(f)
            array('i', ov_vertices).tofile(f)
            for s in ov_sets:
                assert len(s) == len(ov_vertices)
                f.write(bytes(s))


def compile_sim(build):
    os.makedirs(build, exist_ok=True)
    exe = os.path.join(build, 'majsim')
    src = os.path.join(HERE, 'majsim.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-fopenmp', '-Wall', '-o', exe, src], check=True)
    return exe


def run_sim(net, Tmax, probes, build, ov_vertices=(), ov_sets=((),)):
    exe = compile_sim(build)
    with tempfile.TemporaryDirectory(dir=build) as d:
        inp, out = os.path.join(d, 'in.bin'), os.path.join(d, 'out.bin')
        net.dump(inp, Tmax, probes, ov_vertices, ov_sets)
        res = subprocess.run([exe, inp, out], capture_output=True, text=True)
        if res.returncode:
            raise RuntimeError(res.stderr)
        info = json.loads(res.stdout)
        with open(out, 'rb') as f:
            data = f.read()
    W, P = Tmax + 1, len(probes)
    hists = [[data[(s * P + p) * W:(s * P + p + 1) * W] for p in range(P)]
             for s in range(len(ov_sets))]
    return info, hists


def ref_sim(net, Tmax, probes, ov_vertices=(), ov_sets=((),)):
    """Pure-Python simulator with its own timer expansion (small nets only)."""
    state = list(net.state)
    adj = [[] for _ in state]

    def newv(s):
        state.append(s); adj.append([])
        return len(state) - 1

    def link(p, c, k):
        adj[p].append((c, k)); adj[c].append((p, 1))

    for u, v, w in zip(net.au, net.av, net.aw):
        adj[u].append((v, w))
    for i in range(0, len(net.timers), 3):
        r, tau, rising = net.timers[i:i + 3]
        arm, cb = (0, 1) if rising else (1, 0)
        for _ in range(1 if net.compress else 2):
            prev, w = r, (2 if net.compress else 1)
            for _ in range(tau - 1):
                v = newv(arm); link(prev, v, w); w = 1
                c = newv(cb); link(v, c, 1)
                if net.compress:
                    link(c, newv(cb), 2)
                else:
                    link(c, newv(cb), 1); link(c, newv(cb), 1)
                prev = v
            a = newv(cb); link(prev, a, w)
            if net.compress:
                link(a, newv(cb), 2)
            else:
                link(a, newv(cb), 1); link(a, newv(cb), 1)
    deg = [sum(w for _, w in nb) for nb in adj]
    forced = dict(net.forced)
    out = []
    for s in ov_sets:
        x = list(state)
        for v, b in zip(ov_vertices, s):
            x[v] = b
        for v, bits in forced.items():
            x[v] = bits[0]
        hist = [[x[p]] for p in probes]
        for t in range(Tmax):
            y = []
            for v, nb in enumerate(adj):
                c2 = 2 * sum(w * x[u] for u, w in nb)
                y.append(1 if c2 > deg[v] else 0 if c2 < deg[v] else x[v])
            for v, bits in forced.items():
                y[v] = bits[t + 1]
            x = y
            for h, p in zip(hist, probes):
                h.append(x[p])
        out.append([bytes(h) for h in hist])
    return len(state), out


def adversaries(exp, rng):
    """Consumer histories against a port whose target is exp."""
    n = len(exp)
    return {
        'zeros': [0] * n,
        'ones': [1] * n,
        'anti': [1 - exp[t + 1] if t + 1 < n else 0 for t in range(n)],
        'lag': [1 - exp[t] for t in range(n)],
        'rand': [rng.randrange(2) for _ in range(n)],
    }


# ---------------------------------------------------------------- reduction

def cells_of(M):
    names = (['g'] + [('b', i) for i in range(1, M + 1)] + [('c', i) for i in range(1, M + 1)]
             + [('r', i) for i in range(1, M + 1)] + ['cA', 'rA', 'cB', 'rB'])
    edges = ([('g', ('b', 1))] + [(('b', i), ('b', i + 1)) for i in range(1, M)]
             + [(('b', i), ('c', i)) for i in range(1, M + 1)]
             + [(('c', i), ('r', i)) for i in range(1, M + 1)]
             + [('g', 'cA'), ('cA', 'rA'), ('g', 'cB'), ('cB', 'rB')])
    return names, edges


class Program:
    """tree-algorithm.txt section 4; one entry per transition."""

    def __init__(self):
        self.steps = []
        self.cost = {}

    def _op(self, v, mode):
        if 'eval_once' in MUT and mode in (EVAL1, EVAL2):
            self.steps += [{v: mode}, {}]
        elif 'reset_once' in MUT and mode == RESET:
            self.steps += [{v: mode}, {}]
        else:
            self.steps += [{v: mode}, {v: mode}]

    def clear(self, v):
        self._op(v, RESET)

    def copy(self, a, b):
        self.clear(b)
        self._op(b, EVAL1)

    def move(self, a, b):
        self.copy(a, b)
        self.clear(a)

    def store(self, X):
        self.copy('g', 'c' + X); self.copy('c' + X, 'r' + X)
        self.clear('c' + X); self.clear('g')

    def read(self, i, X):
        self.copy(('r', i), ('c', i)); self.copy(('c', i), ('b', i)); self.clear(('c', i))
        for k in range(i, 1, -1):
            self.move(('b', k), ('b', k - 1))
        self.move(('b', 1), 'g')
        self.store(X)

    def gate(self, op):
        self.copy('rA', 'cA'); self.copy('rB', 'cB'); self.clear('g')
        self._op('g', EVAL1 if op == 'OR' else EVAL2)
        self.clear('cA'); self.clear('cB')

    def write(self, i):
        self.move('g', ('b', 1))
        for k in range(1, i):
            self.move(('b', k), ('b', k + 1))
        self.copy(('b', i), ('c', i)); self.copy(('c', i), ('r', i))
        self.clear(('c', i)); self.clear(('b', i))

    def timed(self, name, f, *args):
        n0 = len(self.steps)
        f(*args)
        self.cost.setdefault(name, set()).add((args, len(self.steps) - n0))


def program(circuit):
    """Section 5: READ(p,A); READ(q,B); GATE; WRITE(i); CLEAR(rA); CLEAR(rB)."""
    P = Program()
    for i, node in enumerate(circuit, 1):
        if node[0] == 'IN':
            continue
        op, p, q = node
        n0 = len(P.steps)
        P.timed('READ', P.read, p, 'A')
        P.timed('READ', P.read, q, 'B')
        P.timed('GATE', P.gate, op)
        P.timed('WRITE', P.write, i)
        P.clear('rA'); P.clear('rB')
        P.cost.setdefault('PER_GATE', set()).add(((p, q, i), len(P.steps) - n0))
    return P


class Reduction:
    def __init__(self, circuit, H=None, ever=False):
        self.circuit = list(circuit)
        self.M = M = len(self.circuit)
        self.prog = program(self.circuit)
        self.steps = self.prog.steps
        self.L = len(self.steps)
        self.H = H if H is not None else 100 * M * M + 100
        if self.L + 1 > self.H:
            raise ValueError('H too small')
        self.S = S_of(self.H)
        self.T = self.S + self.H
        self.names, self.edges = cells_of(M)
        self.nbrs = {v: [] for v in self.names}
        for a, b in self.edges:
            self.nbrs[a].append(b); self.nbrs[b].append(a)
        self.out = ('r', M)
        self.ever = ever
        self.q = {v: len(self.nbrs[v]) + (1 if ever and v == self.out else 0) for v in self.names}
        self.inputs = [i for i, nd in enumerate(self.circuit, 1) if nd[0] == 'IN']

    def mode(self, v, idx):
        if idx == 0 or idx > self.L:
            return HOLD
        return self.steps[idx - 1].get(v, HOLD)

    def u(self, v, idx):
        q = self.q[v]
        if 'hold_q' in MUT and self.mode(v, idx) == HOLD:
            return q
        return {HOLD: q + 1, RESET: 0, EVAL1: q + 4, EVAL2: q + 3}[self.mode(v, idx)]

    def idx(self, t):
        return 0 if t < self.S else min(t - self.S, self.H)

    def words(self, v):
        us = [self.u(v, i) for i in range(self.H + 1)]
        groups = {}
        for j in range(1, self.q[v] + 6):
            w = tuple(1 if j <= x else 0 for x in us)
            groups[w] = groups.get(w, 0) + 1
        return groups

    def values(self, bits):
        val, it = [], iter(bits)
        for nd in self.circuit:
            if nd[0] == 'IN':
                val.append(next(it))
            else:
                a, b = val[nd[1] - 1], val[nd[2] - 1]
                val.append(a & b if nd[0] == 'AND' else a | b)
        return val

    def abstract(self, bits, Tmax):
        """Cells, leaves and z with the controls given by the words."""
        cur = {v: 0 for v in self.names}
        for i, b in zip(self.inputs, bits):
            cur[('r', i)] = b
        leaf = dict(cur)
        z = zl = 0
        hist = {v: [cur[v]] for v in self.names}
        zh = [0]
        for t in range(Tmax):
            i = self.idx(t)
            new = {}
            for v in self.names:
                a = sum(cur[w] for w in self.nbrs[v]) + (z if self.ever and v == self.out else 0)
                new[v] = int(a + 4 * leaf[v] + self.u(v, i) >= self.q[v] + 5)
            if self.ever:
                nz = int(cur[self.out] + zl + (1 if t >= self.T + 1 else 0) >= 2)
                zl, z = z, nz
            leaf, cur = cur, new
            for v in self.names:
                hist[v].append(cur[v])
            zh.append(z)
        return hist, zh


def build_reduction(red, compress=True):
    net = Net(compress)
    cell, leaves, ports = {}, {}, {}
    size = 0
    for v in red.names:
        c = net.add(0)
        lv, _, sl = net.hang(c, 4, lambda: net.leaf(0))
        cell[v], leaves[v], ports[v] = c, lv, []
        size += 1 + sl
        for w, k in red.words(v).items():
            h = word_hist(w)
            pp, _, sg = net.hang(c, k, lambda h=h: net.generator(h))
            ports[v].append((w, pp))
            size += sg
    for a, b in red.edges:
        net.link(cell[a], cell[b], 1)
    z = None
    if red.ever:
        z = net.add(0)
        _, _, sl = net.hang(z, 1, lambda: net.leaf(0))
        net.link(cell[red.out], z, 1)
        _, _, st = net.hang(z, 1, lambda: net.timer(red.T + 1, True))
        size += 1 + sl + st
    return net, cell, leaves, ports, z, size


def check_reduction(red, build, compress=True, assignments=None, use_ref=False):
    """Simulate every input assignment; compare ports, cells, output and z."""
    t0 = time.time()
    net, cell, leaves, ports, z, size = build_reduction(red, compress)
    Tmax = red.T + 6
    probes, expect = [], []
    for v in red.names:
        probes.append(cell[v]); expect.append(('cell', v))
        for w, pp in ports[v]:
            for p in pp:
                probes.append(p); expect.append(('port', v, w))
    if z is not None:
        probes.append(z); expect.append(('z',))
    if assignments is None:
        assignments = list(itertools.product((0, 1), repeat=len(red.inputs)))
    ov_v, ov_sets = [], []
    for i in red.inputs:
        ov_v += [cell[('r', i)]] + leaves[('r', i)]
    for bits in assignments:
        s = []
        for b in bits:
            s += [b] * (1 + len(leaves[('r', red.inputs[0])]))
        ov_sets.append(s)
    if not red.inputs:
        ov_sets = [()]
    if use_ref:
        n, hists = ref_sim(net, Tmax, probes, ov_v, ov_sets)
        info = {'n': n}
    else:
        info, hists = run_sim(net, Tmax, probes, build, ov_v, ov_sets)
    port_exp = {}
    failures = []
    for bits, hs in zip(assignments, hists):
        val = red.values(bits)
        ab, zab = red.abstract(bits, Tmax)
        for i in range(1, red.M + 1):
            if ab[('r', i)][red.T] != val[i - 1]:
                failures.append(('abstract register wrong', bits, i))
        for e, h in zip(expect, hs):
            if e[0] == 'cell':
                if list(h) != ab[e[1]]:
                    tbad = next(t for t in range(Tmax + 1) if h[t] != ab[e[1]][t])
                    failures.append(('cell differs from abstract model', bits, str(e[1]), tbad))
            elif e[0] == 'port':
                key = e[2]
                if key not in port_exp:
                    port_exp[key] = bytes(word_expected(key, Tmax))
                if h != port_exp[key]:
                    tbad = next(t for t in range(Tmax + 1) if h[t] != port_exp[key][t])
                    failures.append(('control port differs from its word', bits, str(e[1]), tbad))
            else:
                if list(h) != zab:
                    failures.append(('z differs from abstract model', bits))
                if any(h[: red.T + 2]):
                    failures.append(('z active before T+2', bits))
                if (1 in h) != bool(val[-1]):
                    failures.append(('EVER answer wrong', bits))
        out = hs[expect.index(('cell', red.out))][red.T]
        if out != val[-1]:
            failures.append(('output wrong at T', bits, out, val[-1]))
    res = dict(circuit=red.circuit, M=red.M, L=red.L, H=red.H, S=red.S, T=red.T,
               ever=red.ever, compress=compress, assignments=len(assignments),
               stored_vertices=info['n'], tree_vertices=size,
               seconds=round(time.time() - t0, 2), failures=failures[:20],
               n_failures=len(failures))
    for k in ('links', 'cycles', 'components', 'maxdeg', 'even_degree', 'deg_hist'):
        if k in info:
            res[k] = info[k]
    struct_ok = use_ref or (info['cycles'] == 0 and info['components'] == 1
                            and info['maxdeg'] <= 15 and info['even_degree'] == 0)
    if not use_ref and compress is False and info['n'] != size:
        failures.append(('vertex count mismatch', info['n'], size))
        res['n_failures'] += 1
    res['ok'] = struct_ok and res['n_failures'] == 0
    return res


def all_circuits(M):
    opts = [[('IN',)]]
    for i in range(2, M + 1):
        opts.append([('IN',)] + [(op, p, q) for op in ('AND', 'OR')
                                 for p in range(1, i) for q in range(1, i)])
    return [list(c) for c in itertools.product(*opts)]


def random_circuit(M, rng, n_in):
    c = [('IN',)] * n_in
    for i in range(n_in + 1, M + 1):
        c.append((rng.choice(('AND', 'OR')), rng.randrange(1, i), rng.randrange(1, i)))
    return c


# ---------------------------------------------------------------- unit tests

def test_components(build, report, rng, max_tau=60):
    """Cherries and timers against adversarial consumers, both encodings."""
    for compress in (True, False):
        net = Net(compress)
        Tmax = max_tau + 8
        probes, exps = [], []
        items = [('cherry', b) for b in (0, 1)] + [('timer', tau, r) for tau in range(1, max_tau + 1)
                                                    for r in (True, False)]
        for it in items:
            if it[0] == 'cherry':
                exp = [it[1]] * (Tmax + 1)
            else:
                exp = [int((t >= it[1]) == it[2]) for t in range(Tmax + 1)]
            for name, adv in adversaries(exp, rng).items():
                port = (net.cherry(it[1]) if it[0] == 'cherry' else net.timer(it[1], it[2]))[0]
                e = net.add(adv[0])
                net.link(port, e, 1)
                net.forced.append((e, adv))
                probes.append(port); exps.append((it, name, exp))
        info, hists = run_sim(net, Tmax, probes, build)
        bad = [(str(it), name) for (it, name, exp), h in zip(exps, hists[0]) if list(h) != exp]
        ok = (not bad and info['cycles'] == 0 and info['components'] == len(probes)
              and info['maxdeg'] <= 3 and info['even_degree'] == 0)
        report.append(dict(test='cherries+timers', compress=compress, cases=len(probes),
                           max_tau=max_tau, n=info['n'], maxdeg=info['maxdeg'],
                           even_degree=info['even_degree'], failures=bad[:10], ok=ok))
        if not compress:
            expected_n = sum((3 if it[0] == 'cherry' else 8 * it[1] - 1) + 1
                             for (it, _, _) in exps)
            report[-1]['size_formula_ok'] = expected_n == info['n']
            report[-1]['ok'] = report[-1]['ok'] and expected_n == info['n']


def gen_forest(words, build, rng, compress, advs=('zeros', 'ones', 'anti', 'lag', 'rand'),
               use_ref=False, extra_T=6):
    net = Net(compress)
    Tmax = max(S_of(len(w) - 1) + len(w) - 1 for w in words) + extra_T
    probes, exps, sizes = [], [], []
    for w in words:
        exp = word_expected(w, Tmax)
        av = adversaries(exp, rng)
        for name in advs:
            port, _, size = net.generator(word_hist(w))
            e = net.add(av[name][0])
            net.link(port, e, 1)
            net.forced.append((e, av[name]))
            probes.append(port); exps.append((w, name, exp)); sizes.append(size)
    if use_ref:
        n, hists = ref_sim(net, Tmax, probes)
        info = {'n': n}
    else:
        info, hists = run_sim(net, Tmax, probes, build)
    bad = [(''.join(map(str, w)), name) for (w, name, exp), h in zip(exps, hists[0])
           if list(h) != exp]
    return net, info, bad, len(probes), sizes, hists[0]


def test_generators_exhaustive(build, report, rng, Hmax):
    for H in range(1, Hmax + 1):
        words = [tuple(int(c) for c in format(x, '0%db' % (H + 1))) for x in range(2 ** (H + 1))]
        net, info, bad, cases, sizes, _ = gen_forest(words, build, rng, True)
        ok = (not bad and info['cycles'] == 0 and info['components'] == cases
              and info['maxdeg'] <= 7 and info['even_degree'] == 0)
        report.append(dict(test='generator exhaustive', H=H, words=len(words), cases=cases,
                           n=info['n'], maxdeg=info['maxdeg'], even_degree=info['even_degree'],
                           max_depth=net.stats['max_depth'], min_timer=net.stats['min_timer'],
                           min_leaf_change=net.stats['min_leaf_change'],
                           failures=bad[:10], ok=ok))


def test_generators_random(build, report, rng, configs):
    for H, n_words, kind in configs:
        words = []
        for _ in range(n_words):
            if kind == 'alternating':
                b = rng.randrange(2)
                words.append(tuple((b + t) % 2 for t in range(H + 1)))
            elif kind == 'pairs':
                b = rng.randrange(2)
                words.append(tuple((b + t // 2) % 2 for t in range(H + 1)))
            else:
                p = rng.choice((0.1, 0.3, 0.5, 0.7, 0.9))
                w = [rng.randrange(2)]
                for _ in range(H):
                    w.append(w[-1] ^ (rng.random() < p))
                words.append(tuple(w))
        for compress in (True, False):
            if not compress and H > 40:
                continue
            net, info, bad, cases, sizes, _ = gen_forest(words, build, rng, compress)
            ok = (not bad and info['cycles'] == 0 and info['components'] == cases
                  and info['maxdeg'] <= 7 and info['even_degree'] == 0)
            if not compress:
                ok = ok and info['n'] == sum(sizes) + cases
            Ks = [sum(w[t] != w[t - 1] for t in range(1, H + 1)) for w in words]
            report.append(dict(test='generator random', H=H, kind=kind, words=len(words),
                               K_max=max(Ks), cases=cases, compress=compress, n=info['n'],
                               maxdeg=info['maxdeg'], even_degree=info['even_degree'],
                               max_depth=net.stats['max_depth'],
                               min_timer=net.stats['min_timer'],
                               min_leaf_change=net.stats['min_leaf_change'],
                               max_plain_size=max(sizes), failures=bad[:10], ok=ok))


def test_reference(build, report, rng):
    """majsim against the pure-Python simulator, both encodings."""
    words = [tuple(rng.randrange(2) for _ in range(H + 1)) for H in (1, 2, 3, 5, 8, 12)]
    words += [tuple(t % 2 for t in range(13)), tuple((t // 2) % 2 for t in range(11))]
    for compress in (True, False):
        r1 = gen_forest(words, build, random.Random(7), compress)
        r2 = gen_forest(words, build, random.Random(7), compress, use_ref=True)
        same = r1[5] == r2[5] and r1[1]['n'] == r2[1]['n']
        report.append(dict(test='majsim vs python simulator (generators)', compress=compress,
                           cases=r1[3], n=r1[1]['n'], identical=same,
                           failures=r1[2][:5] + r2[2][:5], ok=same and not r1[2] and not r2[2]))
    red = Reduction([('IN',), ('IN',), ('AND', 1, 2)], H=None)
    red = Reduction(red.circuit, H=red.L + 1)
    a = check_reduction(red, build, compress=True, assignments=[(1, 1), (0, 1)])
    b = check_reduction(red, build, compress=True, assignments=[(1, 1), (0, 1)], use_ref=True)
    report.append(dict(test='majsim vs python simulator (reduction M=3, H=L+1)',
                       ok=a['ok'] and b['ok'], majsim=a, python=b))


def test_uniformity(report, rng, configs):
    """(G4), (G5), (G6), depth, first leaf change and timer dates."""
    for H, n_words in configs:
        bad, nodes, worst_depth = [], 0, 0
        for _ in range(n_words):
            kind = rng.randrange(3)
            if kind == 0:
                w = [rng.randrange(2) for _ in range(H + 1)]
            elif kind == 1:
                b = rng.randrange(2); w = [(b + t) % 2 for t in range(H + 1)]
            else:
                w = [rng.randrange(2)]
                for _ in range(H):
                    w.append(w[-1] ^ (rng.random() < 0.2))
            root = word_hist(w)
            S, D = S_of(H), (H + 1).bit_length()
            stack = [((), root)]
            while stack:
                path, h = stack.pop()
                nodes += 1
                d = len(path)
                worst_depth = max(worst_depth, d)
                Kp = root.K
                for j in path:
                    Kp = g_closed(j, Kp)
                if Kp != h.K:
                    bad.append(('K', path))
                b0 = root.b0 ^ (sum(j == 0 for j in path) & 1)
                if b0 != h.b0:
                    bad.append(('initial bit', path))
                for t in range(0, H + S + 3):
                    qp = root.q(t + d)
                    for j in path:
                        qp = g_closed(j, qp)
                    if qp != h.q(t) or (b0 ^ (qp & 1)) != h.at(t):
                        bad.append(('G6', path, t))
                        break
                if d > D:
                    bad.append(('depth > D', path))
                if h.K <= 4:
                    if h.K and h.ch[0] < 9:
                        bad.append(('leaf change < 9', path, h.ch[0]))
                    continue
                if d > (h.K + 1).bit_length() + 64:
                    bad.append(('runaway', path))
                for j in range(4):
                    c = h.child(j)
                    if c.K > h.K // 2 + 1:
                        bad.append(('G5', path, j))
                    for t in range(0, H + S + 2):
                        if c.at(t) != h.at(t + 1) ^ int(j == h.q(t + 1) % 4):
                            bad.append(('G3', path, j, t))
                            break
                    stack.append((path + (j,), c))
        report.append(dict(test='uniformity formulas', H=H, words=n_words, nodes=nodes,
                           max_depth=worst_depth, D=(H + 1).bit_length(),
                           failures=bad[:10], ok=not bad))


def test_depth(report, Kmax=10 ** 6):
    """hardness.txt section 6: depth <= ceil(log2(K+1)) and (G5), every K <= Kmax."""
    import functools, math
    sys.setrecursionlimit(10000)

    @functools.lru_cache(None)
    def depth(K):
        return 0 if K <= 4 else 1 + max(depth(g_closed(j, K)) for j in range(4))

    @functools.lru_cache(None)
    def leaves(K):
        return 1 if K <= 4 else sum(leaves(g_closed(j, K)) for j in range(4))

    bad, ratio = [], 0.0
    for K in range(Kmax + 1):
        if K and depth(K) > math.ceil(math.log2(K + 1)):
            bad.append(('depth', K))
        if any(g_closed(j, K) > K // 2 + 1 for j in range(4)):
            bad.append(('G5', K))
        if K > 4 and K % 997 == 0:
            ratio = max(ratio, leaves(K) / (K + 1) ** 2)
    report.append(dict(test='recursion depth and child changes', K_max=Kmax,
                       depth_at_K_max=depth(Kmax), max_leaves_over_K1_squared_sampled=round(ratio, 4),
                       failures=bad[:10], ok=not bad))


def test_word_changes(report, rng):
    """Changes per control word and largest timer date versus M (size remark)."""
    rows = []
    for M in (4, 8, 16, 32, 48):
        worst = 0
        for _ in range(3):
            red = Reduction(random_circuit(M, rng, max(1, M // 4)))
            for v in red.names:
                us = [red.u(v, i) for i in range(red.L + 2)]
                for j in range(1, red.q[v] + 6):
                    w = [1 if j <= x else 0 for x in us]
                    worst = max(worst, sum(w[t] != w[t - 1] for t in range(1, len(w))))
        rows.append(dict(M=M, L=red.L, K_max=worst, K_max_over_M=round(worst / M, 2),
                         last_change_time=red.S + red.L + 1, H=red.H))
    report.append(dict(test='control word changes versus M', rows=rows, ok=True))


def test_cell(build, report, rng, n_programs=40):
    """A memory cell with q forced (adversarial) data neighbours and real
    generators as controls: HOLD/RESET/EVAL against random programs."""
    for q in (1, 2, 3):
        for compress in (True, False):
            fails, checks = [], 0
            for trial in range(n_programs):
                ops, modes, data, expect = [], [HOLD], [], []
                bit0 = rng.randrange(2)
                cur = bit0
                quiescent0 = cur == 0
                while len(modes) < 120:
                    r = rng.random()
                    if r < 0.35:
                        k = rng.randrange(1, 5)
                        modes += [HOLD] * k
                        data += [None] * k
                        expect += [cur] * k
                    elif r < 0.6 or not quiescent0:
                        modes += [RESET, RESET]; data += [None, None]
                        cur = 0; quiescent0 = True
                        expect += [0, 0]
                    else:
                        rr = 1 if rng.random() < 0.5 else 2
                        a = [rng.randrange(2) for _ in range(q)]
                        modes += [EVAL1 if rr == 1 else EVAL2] * 2
                        data += [a, a]
                        cur = int(sum(a) >= rr); quiescent0 = cur == 0
                        expect += [cur, cur]
                modes += [HOLD] * 4; data += [None] * 4; expect += [cur] * 4
                Hc = len(modes) - 1
                S = S_of(Hc)
                Tmax = S + Hc + 3
                u = {HOLD: q + 1, RESET: 0, EVAL1: q + 4, EVAL2: q + 3}
                net = Net(compress)
                v = net.add(bit0)
                net.hang(v, 4, lambda: net.leaf(bit0))
                groups = {}
                for j in range(1, q + 6):
                    w = tuple(int(j <= u[m]) for m in modes)
                    groups[w] = groups.get(w, 0) + 1
                for w, k in groups.items():
                    net.hang(v, k, lambda w=w: net.generator(word_hist(w)))
                # data neighbours: random except during EVAL (word index i
                # controls the transition from physical time S+i)
                seqs = [[rng.randrange(2) for _ in range(Tmax + 1)] for _ in range(q)]
                for i, d in enumerate(data):
                    if d is not None:
                        for k in range(q):
                            seqs[k][S + i + 1] = d[k]
                for k in range(q):
                    e = net.add(seqs[k][0])
                    net.link(v, e, 1)
                    net.forced.append((e, seqs[k]))
                info, hists = run_sim(net, Tmax, [v], build)
                h = hists[0][0]
                # modes[i] (i >= 1) gives the value at physical time S+i+1
                for i in range(1, len(modes)):
                    e = expect[i - 1]
                    if e is not None:
                        checks += 1
                        if h[S + i + 1] != e:
                            fails.append((trial, i, modes[i], e, h[S + i + 1]))
                if any(h[t] != bit0 for t in range(S + 2)):
                    fails.append((trial, 'prefix'))
                if info['maxdeg'] > 2 * q + 9 or info['even_degree']:
                    fails.append((trial, 'degree', info['maxdeg'], info['even_degree']))
            report.append(dict(test='memory cell, adversarial data neighbours', q=q,
                               compress=compress, programs=n_programs, checks=checks,
                               failures=fails[:10], ok=not fails))


def test_costs(report):
    """Durations stated in tree-algorithm.txt section 5."""
    bad = []
    for M in range(1, 9):
        for c in all_circuits(M) if M <= 3 else [random_circuit(M, random.Random(M), 2)]:
            P = program(c)
            for (args, n) in P.cost.get('READ', ()):
                if n != 6 * args[0] + 22:
                    bad.append(('READ', args, n))
            for (args, n) in P.cost.get('GATE', ()):
                if n != 16:
                    bad.append(('GATE', n))
            for (args, n) in P.cost.get('WRITE', ()):
                if n != 6 * args[0] + 12:
                    bad.append(('WRITE', args, n))
            for (pqi, n) in P.cost.get('PER_GATE', ()):
                p, q, i = pqi
                if n != 6 * (p + q + i) + 76 or n > 18 * M + 76:
                    bad.append(('gate', pqi, n))
            L = len(P.steps)
            if L > 18 * M * M + 76 * M or L > 94 * M * M or L + 1 > 100 * M * M + 100:
                bad.append(('L', M, L))
    report.append(dict(test='program costs', failures=bad[:10], ok=not bad))


def test_mutations(build, report, rng):
    """Each deliberate defect must be detected (the harness is not vacuous)."""
    circuits = [[('IN',), ('IN',), ('AND', 1, 2)], [('IN',), ('IN',), ('OR', 2, 1)],
                [('IN',), ('OR', 1, 1), ('AND', 2, 1)]]
    words = [tuple(rng.randrange(2) for _ in range(H + 1)) for H in (6, 9, 12, 20)]
    words += [tuple(t % 2 for t in range(17))]
    for m in ('hold_q', 'eval_once', 'reset_once', 'no_advance', 'child_no_shift', 'single_copy'):
        MUT.clear(); MUT.add(m)
        detected, how = False, []
        try:
            _, info, bad, _, _, _ = gen_forest(words, build, rng, True)
            if bad or info['even_degree'] or info['maxdeg'] > 7:
                detected = True; how.append('generator test: %d failures' % len(bad))
            for c in circuits:
                red = Reduction(c)
                red = Reduction(c, H=red.L + 1)
                r = check_reduction(red, build)
                if not r['ok']:
                    detected = True
                    how.append('reduction %s: %s' % (c, r['failures'][:1]))
        except ValueError as e:
            detected = True; how.append('construction refused: %s' % e)
        finally:
            MUT.clear()
        report.append(dict(test='mutation detected', mutation=m, detected=detected,
                           how=how[:3], ok=detected))


def test_bzz(build, report):
    """Benjamini-Zakharov-Zhukovskii (arXiv:2507.04714, Thm 1.1): on a finite
    tree with odd degrees the worst-case stabilisation time is the largest
    t(Q) over paths Q of active vertices.  A timer of date tau contains such a
    path with 2*tau - 1 vertices (both arms and the port), so the observed
    stabilisation time must not exceed 2*tau_max - 1 if the theorem applies."""
    cases = [([('IN',), ('IN',), ('AND', 1, 2)], None, False),
             ([('IN',), ('IN',), ('AND', 1, 2)], None, True),
             ([('IN',), ('IN',), ('OR', 1, 2), ('AND', 3, 1), ('OR', 4, 2), ('AND', 5, 3)], 'min', False)]
    os.environ['MAJSIM_TRANSIENT'] = '1'
    try:
        for c, H_rule, ever in cases:
            red = Reduction(c, ever=ever)
            if H_rule == 'min':
                red = Reduction(c, H=red.L + 1, ever=ever)
            net, cell, leaves, ports, z, size = build_reduction(red)
            ov_v = []
            for i in red.inputs:
                ov_v += [cell[('r', i)]] + leaves[('r', i)]
            sets = [[b] * len(ov_v) for b in (0, 1)]
            info, _ = run_sim(net, red.T + 60, [cell[red.out]], build, ov_v, sets)
            bound = 2 * net.stats['max_timer'] - 1
            stab = info['stabilization']
            ok = all(0 <= s_ <= bound for s_ in stab)
            report.append(dict(test='stabilisation time vs BZZ path bound', circuit=c, M=red.M,
                               H=red.H, S=red.S, L=red.L, T=red.T, ever=ever,
                               program_end=red.S + red.L + 1, max_timer_date=net.stats['max_timer'],
                               stabilization=stab, bzz_lower_bound_2tau_minus_1=bound,
                               tree_vertices=size, ok=ok))
    finally:
        os.environ.pop('MAJSIM_TRANSIENT', None)


def run_reductions(build, report, circuits, label, H_rule='min', ever=(False, True),
                   compress=True):
    for c in circuits:
        for e in ever:
            red = Reduction(c, ever=e)
            if H_rule == 'min':
                red = Reduction(c, H=red.L + 1, ever=e)
            report.append(dict(test=label, **check_reduction(red, build, compress=compress)))
            if not report[-1]['ok']:
                print(json.dumps(report[-1], default=str)[:2000], flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--build', default=os.path.join(tempfile.gettempdir(), 'treered-build'))
    ap.add_argument('--out', default=None, help='JSON report')
    ap.add_argument('--quick', action='store_true',
                    help='smaller unit tests; skip M = 4, random, spec-H and plain-tree reductions')
    ap.add_argument('--only', nargs='*', default=None)
    ap.add_argument('--seed', type=int, default=20261006)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    report = []
    t0 = time.time()

    heavy = {'reduction-explicit', 'reduction-spec', 'reduction-m4', 'reduction-random'}

    def want(name):
        if args.only is not None:
            return name in args.only
        return not (args.quick and name in heavy)

    if want('costs'):
        test_costs(report)
    if want('reference'):
        test_reference(args.build, report, rng)
    if want('components'):
        test_components(args.build, report, rng, 40 if args.quick else 120)
    if want('uniformity'):
        test_uniformity(report, rng, [(12, 200), (40, 100), (200, 30)] if not args.quick else [(20, 50)])
    if want('generators'):
        test_generators_exhaustive(args.build, report, rng, 7 if args.quick else 10)
        test_generators_random(args.build, report, rng,
                               [(20, 30, 'random'), (24, 6, 'alternating')] if args.quick else
                               [(16, 60, 'random'), (32, 30, 'random'), (30, 6, 'alternating'),
                                (30, 6, 'pairs'), (64, 10, 'random'), (64, 3, 'alternating'),
                                (128, 4, 'random'), (100, 2, 'alternating')])
    if want('depth'):
        test_depth(report, 10 ** 4 if args.quick else 10 ** 6)
    if want('words'):
        test_word_changes(report, rng)
    if want('cell'):
        test_cell(args.build, report, rng, 10 if args.quick else 40)
    if want('mutations'):
        test_mutations(args.build, report, rng)
    if want('bzz'):
        test_bzz(args.build, report)
    if want('reduction'):
        circ = [c for M in (1, 2, 3) for c in all_circuits(M)]
        run_reductions(args.build, report, circ, 'reduction M<=3 exhaustive, H = L+1')
    if want('reduction-explicit'):
        circ = [[('IN',), ('IN',), ('AND', 1, 2)], [('IN',), ('IN',), ('OR', 2, 1)],
                [('IN',), ('AND', 1, 1), ('OR', 2, 1)]]
        run_reductions(args.build, report, circ, 'reduction plain tree (no compression), H = L+1',
                       compress=False)
    if want('reduction-spec'):
        circ = [c for M in (1, 2, 3) for c in all_circuits(M)]
        run_reductions(args.build, report, circ, 'reduction M<=3 exhaustive, H = 100M^2+100',
                       H_rule='spec')
    if want('reduction-m4'):
        run_reductions(args.build, report, all_circuits(4), 'reduction M=4 exhaustive, H = L+1')
    if want('reduction-random'):
        r2 = random.Random(args.seed + 1)
        circ = [random_circuit(M, r2, r2.randrange(1, 4)) for M in (5, 6, 7, 8) for _ in range(3)]
        run_reductions(args.build, report, circ, 'reduction random M=5..8, H = L+1')
        circ = [random_circuit(M, r2, 2) for M in (4, 5)]
        run_reductions(args.build, report, circ, 'reduction random M=4..5, H = 100M^2+100',
                       H_rule='spec')
    ok = all(r.get('ok') for r in report)
    summary = dict(ok=ok, tests=len(report), failed=[i for i, r in enumerate(report) if not r.get('ok')],
                   seconds=round(time.time() - t0, 1))
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(dict(summary=summary, report=report), f, indent=1, default=str)
    for r in report:
        brief = {k: r[k] for k in r if k in ('test', 'H', 'M', 'q', 'compress', 'kind', 'cases',
                                              'words', 'n', 'stored_vertices', 'tree_vertices',
                                              'rows', 'depth_at_K_max', 'stabilization',
                                              'ok', 'n_failures', 'seconds')}
        print(json.dumps(brief, default=str))
    print(json.dumps(summary))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
