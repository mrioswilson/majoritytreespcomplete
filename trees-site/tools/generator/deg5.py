#!/usr/bin/env python3
"""Independent check of the degree-5 tree reduction of
research/majority-degree-20261006 (hardness-degree.txt, degree-review.txt).

Re-implemented from the text of the notes:
  pulses P[a,b) and their complements (degree-review.txt section 1);
  the word generator of degree 5: four-child recursion while K > 2, bases
  with at most two changes (section 2);
  macrocells A-C-B with leaves A', B', one external port and two controls per
  main node (hardness-degree.txt section 2);
  port assignment on the bus skeleton (section 3);
  CLEAR/COPY/MOVE/STORE/READ/WRITE and the 27-step GATE (sections 4-5);
  H = 200M^2+200, S, T and the EVER receiver (sections 6, 8).
Simulation uses majsim.c and the Net encoding of
research/adversarial-trees-review-20261006/treered.py (both unmodified).
"""
import argparse
import itertools
import json
import os
import random
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'adversarial-trees-review-20261006'))
import treered as tr  # noqa: E402
from treered import (Net, S_of, word_hist, word_expected, adversaries, run_sim,  # noqa: E402
                     ref_sim, cells_of, all_circuits, random_circuit)

MUT = set()   # deliberate defects, used only by test_mutations
HOLD, RESET, LOAD = (1, 1, 1), (0, 0, 0), (2, 2, 2)
ALL_ADV = ('zeros', 'ones', 'anti', 'lag', 'rand')
NODES = 'ACB'


# ---------------------------------------------------------------- generator

def pulse(net, a, b, neg=False):
    """P[a,b) = [a <= t < b], 1 <= a < b (complement if neg).  Chain of a
    roots; root at level l has children D_{b-l-1}, 0, U_{a-l-1}, next root,
    and the last one D_{b-a}, 0, 1, D_{b-a}."""
    if not 1 <= a < b:
        raise ValueError('pulse needs 1 <= a < b, got %d, %d' % (a, b))
    top = prev = None
    total = 0
    s = net.stats
    s['pulses'] = s.get('pulses', 0) + 1
    s['max_pulse_a'] = max(s.get('max_pulse_a', 0), a)
    shift = 0 if 'pulse_no_shift' in MUT else 1
    for level in range(a):
        aa, bb = a - level, b - level
        r = net.add(1 if neg else 0)
        if prev is None:
            top = r
        else:
            net.link(prev, r, 1)
        size = 1
        _, _, x = net.hang(r, 2 if aa == 1 else 1, lambda bb=bb: net.timer(bb - shift, neg))
        size += x
        _, _, x = net.hang(r, 1, lambda: net.cherry(1 if neg else 0))
        size += x
        if aa == 1:
            _, _, x = net.hang(r, 1, lambda: net.cherry(0 if neg else 1))
        else:
            _, _, x = net.hang(r, 1, lambda aa=aa: net.timer(aa - shift, not neg))
        size += x
        total += size
        prev = r
    return top, (1 if neg else 0), total


def generator5(net, h, depth=0):
    """Four-child recursion while K > 2; bases: cherry, timer, pulse."""
    s = net.stats
    s['max_depth'] = max(s['max_depth'], depth)
    if h.K <= 2:
        s['leaves'] += 1
        if h.K:
            m = s['min_leaf_change']
            s['min_leaf_change'] = h.ch[0] if m is None else min(m, h.ch[0])
        if h.K == 0:
            return net.cherry(h.b0)
        if h.K == 1:
            return net.timer(h.ch[0], h.b0 == 0)
        return pulse(net, h.ch[0], h.ch[1], neg=(h.b0 == 1))
    r = net.add(h.b0)
    s['nodes'] += 1
    size = 1
    for j in range(4):
        _, _, sz = net.hang(r, 1, lambda c=h.child(j): generator5(net, c, depth + 1))
        size += sz
    return r, h.b0, size


# ---------------------------------------------------------------- program

class Program5:
    """hardness-degree.txt sections 4-6; one entry per transition, each entry
    maps a macrocell to the control counts (u_A, u_C, u_B)."""

    def __init__(self):
        self.steps = []
        self.cost = {}

    def put(self, n, modes):
        self.steps += [dict(modes) for _ in range(n)]

    def reset(self, v, extra=None):
        n = 3 if 'reset3' in MUT else 4
        m = {v: RESET}
        m.update(extra or {})
        self.put(n, m)

    def clear(self, v):
        self.reset(v)

    def copy(self, a, b, extra=None):
        self.reset(b, extra)
        m = {b: LOAD}
        m.update(extra or {})
        self.put(3 if 'load3' in MUT else 4, m)

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
        uc = 1 if op == 'AND' else 2
        g0 = {'g': RESET}
        self.copy('rA', 'cA', g0)                       # phase 0: 16 steps
        self.copy('rB', 'cB', g0)
        self.put(2, {'g': (2, 0, 2)})                   # phase 1
        self.put(1, {'g': (1, uc, 1)})                  # phase 2
        self.put(4, {'g': (1, uc, 1), 'cA': RESET, 'cB': RESET})   # phase 3
        if 'gate_no_phase4' not in MUT:
            self.put(2, {'g': (1, uc, 1)})              # phase 4
        last = (1, uc, 1) if 'gate_phase5_hold' in MUT else (2, uc, 2)
        self.put(2, {'g': last})                        # phase 5

    def write(self, i):
        self.move('g', ('b', 1))
        for k in range(1, i):
            self.move(('b', k), ('b', k + 1))
        self.copy(('b', i), ('c', i)); self.copy(('c', i), ('r', i))
        self.clear(('c', i)); self.clear(('b', i))

    def cleanup(self):
        self.clear('rA'); self.clear('rB')

    def timed(self, name, f, *args):
        n0 = len(self.steps)
        f(*args)
        self.cost.setdefault(name, set()).add((args, len(self.steps) - n0))


def program5(circuit):
    """READ(p,A); READ(q,B); GATE; WRITE(i); CLEAR(rA); CLEAR(rB) per gate."""
    P = Program5()
    checkpoints = []
    for i, nd in enumerate(circuit, 1):
        if nd[0] == 'IN':
            continue
        op, p, q = nd
        n0 = len(P.steps)
        P.timed('READ', P.read, p, 'A')
        P.timed('READ', P.read, q, 'B')
        P.timed('GATE', P.gate, op)
        P.timed('WRITE', P.write, i)
        P.timed('CLEAN', P.cleanup)
        P.cost.setdefault('PER_GATE', set()).add(((p, q, i), len(P.steps) - n0))
        checkpoints.append((len(P.steps), i))
    return P.steps, checkpoints, P.cost


def port_assignment(M):
    """hardness-degree.txt section 3: logical edge (u, v) -> main node of u."""
    P = {('g', 'cA'): 'A', ('g', 'cB'): 'B', ('g', ('b', 1)): 'C'}
    for i in range(1, M + 1):
        b, c, r = ('b', i), ('c', i), ('r', i)
        pred = 'g' if i == 1 else ('b', i - 1)
        P[(b, pred)] = 'A'
        if i < M:
            P[(b, ('b', i + 1))] = 'B'
            P[(b, c)] = 'C'
        else:
            P[(b, c)] = 'B'           # two neighbours: A, B; C gets a constant 0
        P[(c, b)] = 'A'
        P[(c, r)] = 'B'
        P[(r, c)] = 'A'
    for X in 'AB':
        P[('c' + X, 'g')] = 'A'
        P[('c' + X, 'r' + X)] = 'B'
        P[('r' + X, 'c' + X)] = 'A'
    return P


class Reduction5:
    def __init__(self, circuit, H=None, ever=False):
        self.circuit = [tuple(n) for n in circuit]
        self.M = M = len(self.circuit)
        self.steps, self.checkpoints, self.cost = program5(self.circuit)
        self.L = len(self.steps)
        self.H = H if H is not None else 200 * M * M + 200
        if self.L + 1 > self.H:
            raise ValueError('H too small')
        self.S = S_of(self.H)
        self.T = self.S + self.H
        self.names, self.edges = cells_of(M)
        self.port = port_assignment(M)
        for a, b in self.edges:
            assert (a, b) in self.port and (b, a) in self.port, (a, b)
        self.out = ('r', M)
        self.ever = ever
        self.inputs = [i for i, nd in enumerate(self.circuit, 1) if nd[0] == 'IN']

    def u(self, v, xi, idx):
        if idx == 0 or idx > self.L:
            return 1
        return self.steps[idx - 1].get(v, HOLD)[xi]

    def node_words(self, v, xi):
        us = [self.u(v, xi, i) for i in range(self.H + 1)]
        groups = {}
        for j in (1, 2):
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

    def expected_cells(self, bits, done):
        """Register contents once gates <= done are processed; all else 0."""
        val = self.values(bits)
        exp = {v: 0 for v in self.names}
        for i, nd in enumerate(self.circuit, 1):
            if nd[0] == 'IN' or i <= done:
                exp[('r', i)] = val[i - 1]
        return exp


def build5(red, compress=True, controls='gen'):
    """The tree of the reduction.  controls='gen' hangs the real degree-5
    generators; controls='forced' replaces each control by a forced vertex
    that follows its word (exact majority on all macrocells, abstract clocks)."""
    net = Net(compress)
    cell, ports = {}, {}
    size = 0
    Tmax = red.T + 6
    for v in red.names:
        node = {X: net.add(0) for X in NODES}
        node['a'], node['b'] = net.add(0), net.add(0)
        net.link(node['A'], node['C']); net.link(node['C'], node['B'])
        net.link(node['A'], node['a']); net.link(node['B'], node['b'])
        size += 5
        for xi, X in enumerate(NODES):
            for w, k in red.node_words(v, xi).items():
                if controls == 'gen':
                    pp, _, s = net.hang(node[X], k, lambda w=w: generator5(net, word_hist(w)))
                    size += s
                else:
                    seq = word_expected(w, Tmax)
                    e = net.add(seq[0])
                    net.link(node[X], e, k)
                    net.forced.append((e, seq))
                    pp = [e]
                ports.setdefault((v, X), []).append((w, pp))
        cell[v] = node
    used = set()
    for a, b in red.edges:
        Xa, Xb = red.port[(a, b)], red.port[(b, a)]
        net.link(cell[a][Xa], cell[b][Xb], 1)
        used.add((a, Xa)); used.add((b, Xb))
    z = None
    if red.ever:
        z = net.add(0)
        net.hang(z, 1, lambda: net.leaf(0))
        net.link(cell[red.out]['B'], z, 1)
        used.add((red.out, 'B'))
        _, _, st = net.hang(z, 1, lambda: net.timer(red.T + 1, True))
        size += 2 + st
    for v in red.names:
        for X in NODES:
            if (v, X) not in used:
                _, _, s = net.hang(cell[v][X], 1, lambda: net.cherry(0))
                size += s
    return net, cell, ports, z, size


def check5(red, build, compress=True, controls='gen', assignments=None, compare=None):
    """Simulate every input assignment and check: structure; every control
    port equals its word; at each gate checkpoint, every macrocell is
    quiescent with the register contents of the circuit; output and EVER.
    compare: histories of a 'forced' run to match vertex by vertex."""
    t0 = time.time()
    net, cell, ports, z, size = build5(red, compress, controls)
    Tmax = red.T + 6
    probes, tags = [], []
    for v in red.names:
        for X in 'ACBab':
            probes.append(cell[v][X]); tags.append(('cell', v, X))
    if controls == 'gen':
        for (v, X), lst in ports.items():
            for w, pp in lst:
                for p in pp:
                    probes.append(p); tags.append(('port', v, X, w))
    if z is not None:
        probes.append(z); tags.append(('z',))
    if assignments is None:
        assignments = list(itertools.product((0, 1), repeat=len(red.inputs)))
    ov_v = [cell[('r', i)][X] for i in red.inputs for X in 'ACBab']
    ov_sets = [[b for b in bits for _ in range(5)] for bits in assignments] or [()]
    info, hists = run_sim(net, Tmax, probes, build, ov_v, ov_sets)
    failures = []
    wexp = {}
    cell_hist = []
    for bits, hs in zip(assignments, hists):
        val = red.values(bits)
        by = {}
        for tag, h in zip(tags, hs):
            if tag[0] == 'cell':
                by[(tag[1], tag[2])] = h
            elif tag[0] == 'port':
                w = tag[3]
                if w not in wexp:
                    wexp[w] = bytes(word_expected(w, Tmax))
                if h != wexp[w]:
                    tb = next(t for t in range(Tmax + 1) if h[t] != wexp[w][t])
                    failures.append(('control port differs from its word', bits, str(tag[1]), tag[2], tb))
            else:
                if any(h[: red.T + 2]):
                    failures.append(('z active before T+2', bits))
                if (1 in h) != bool(val[-1]):
                    failures.append(('EVER answer wrong', bits))
        cell_hist.append(by)
        marks = [(red.S + 1, 0)] + [(red.S + s + 1, i) for s, i in red.checkpoints] + [(red.T, red.M)]
        for t, done in marks:
            exp = red.expected_cells(bits, done)
            for v in red.names:
                got = [by[(v, X)][t] for X in 'ACBab']
                if got != [exp[v]] * 5:
                    failures.append(('cell wrong at checkpoint', bits, str(v), t, done, got, exp[v]))
                    break
        out = [by[(red.out, X)][red.T] for X in 'ACB']
        if out != [val[-1]] * 3:
            failures.append(('output wrong at T', bits, out, val[-1]))
    if compare is not None:
        for a, (by, ref) in enumerate(zip(cell_hist, compare)):
            for key, h in by.items():
                if h != ref[key]:
                    tb = next(t for t in range(Tmax + 1) if h[t] != ref[key][t])
                    failures.append(('cell differs from forced-control run', assignments[a], str(key), tb))
                    break
    res = dict(circuit=red.circuit, M=red.M, L=red.L, H=red.H, S=red.S, T=red.T, ever=red.ever,
               controls=controls, compress=compress, assignments=len(assignments),
               stored_vertices=info['n'], tree_vertices=size, seconds=round(time.time() - t0, 2),
               failures=failures[:20], n_failures=len(failures))
    for k in ('links', 'cycles', 'components', 'maxdeg', 'even_degree', 'deg_hist'):
        res[k] = info.get(k)
    struct_ok = (info['cycles'] == 0 and info['components'] == 1 and info['maxdeg'] <= 5
                 and info['even_degree'] == 0)
    if controls == 'gen' and not compress and info['n'] != size:
        failures.append(('vertex count mismatch', info['n'], size))
        res['n_failures'] += 1
    res['ok'] = struct_ok and res['n_failures'] == 0
    return res, cell_hist


# ---------------------------------------------------------------- unit tests

def test_pulses(build, report, rng, Bmax):
    for compress in (True, False):
        net = Net(compress)
        Tmax = Bmax + 4
        probes, exps, sizes = [], [], []
        for b in range(2, Bmax + 1):
            for a in range(1, b):
                for neg in (False, True):
                    exp = [int((a <= t < b) != neg) for t in range(Tmax + 1)]
                    for name, adv in adversaries(exp, rng).items():
                        port, _, size = pulse(net, a, b, neg)
                        e = net.add(adv[0])
                        net.link(port, e, 1)
                        net.forced.append((e, adv))
                        probes.append(port); exps.append(((a, b, neg), name, exp)); sizes.append(size)
        info, hists = run_sim(net, Tmax, probes, build)
        bad = [(str(k), name) for (k, name, exp), h in zip(exps, hists[0]) if list(h) != exp]
        ok = (not bad and info['cycles'] == 0 and info['components'] == len(probes)
              and info['maxdeg'] <= 5 and info['even_degree'] == 0)
        if not compress:
            ok = ok and info['n'] == sum(sizes) + len(probes)
        report.append(dict(test='pulses P[a,b) and complements, 5 adversaries', compress=compress,
                           b_max=Bmax, cases=len(probes), n=info['n'], maxdeg=info['maxdeg'],
                           even_degree=info['even_degree'], max_plain_size=max(sizes),
                           failures=bad[:10], ok=ok))


def gen_forest5(words, build, rng, compress, advs=('zeros', 'ones', 'anti', 'lag', 'rand')):
    net = Net(compress)
    Tmax = max(S_of(len(w) - 1) + len(w) - 1 for w in words) + 6
    probes, exps, sizes = [], [], []
    for w in words:
        exp = word_expected(w, Tmax)
        av = adversaries(exp, rng)
        for name in advs:
            port, _, size = generator5(net, word_hist(w))
            e = net.add(av[name][0])
            net.link(port, e, 1)
            net.forced.append((e, av[name]))
            probes.append(port); exps.append((w, name, exp)); sizes.append(size)
    info, hists = run_sim(net, Tmax, probes, build)
    bad = [(''.join(map(str, w)), name) for (w, name, exp), h in zip(exps, hists[0]) if list(h) != exp]
    return net, info, bad, len(probes), sizes


def test_generators5(build, report, rng, Hmax, configs):
    for H in range(1, Hmax + 1):
        words = [tuple(int(c) for c in format(x, '0%db' % (H + 1))) for x in range(2 ** (H + 1))]
        advs = (('zeros', 'ones', 'anti', 'lag', 'rand') if H <= 6 else
                ('anti', 'lag', 'rand') if H <= 8 else ('anti',))
        net, info, bad, cases, sizes = gen_forest5(words, build, rng, True, advs)
        ok = (not bad and info['cycles'] == 0 and info['components'] == cases
              and info['maxdeg'] <= 5 and info['even_degree'] == 0)
        report.append(dict(test='degree-5 generator, all words', H=H, words=len(words), cases=cases,
                           n=info['n'], maxdeg=info['maxdeg'], even_degree=info['even_degree'],
                           max_depth=net.stats['max_depth'], min_leaf_change=net.stats['min_leaf_change'],
                           min_timer=net.stats['min_timer'], failures=bad[:10], ok=ok))
    for H, n_words, kind, advs in configs:
        words = []
        for _ in range(n_words):
            b = rng.randrange(2)
            if kind == 'alternating':
                words.append(tuple((b + t) % 2 for t in range(H + 1)))
            elif kind == 'pairs':
                words.append(tuple((b + t // 2) % 2 for t in range(H + 1)))
            else:
                p = rng.choice((0.1, 0.3, 0.5, 0.7, 0.9))
                w = [b]
                for _ in range(H):
                    w.append(w[-1] ^ (rng.random() < p))
                words.append(tuple(w))
        for compress in ((True, False) if H <= 16 else (True,)):
            net, info, bad, cases, sizes = gen_forest5(words, build, rng, compress, advs)
            ok = (not bad and info['cycles'] == 0 and info['components'] == cases
                  and info['maxdeg'] <= 5 and info['even_degree'] == 0)
            if not compress:
                ok = ok and info['n'] == sum(sizes) + cases
            Ks = [sum(w[t] != w[t - 1] for t in range(1, H + 1)) for w in words]
            report.append(dict(test='degree-5 generator, sampled words', H=H, kind=kind, words=len(words),
                               K_max=max(Ks), cases=cases, compress=compress, n=info['n'],
                               maxdeg=info['maxdeg'], even_degree=info['even_degree'],
                               max_depth=net.stats['max_depth'],
                               min_leaf_change=net.stats['min_leaf_change'],
                               max_plain_size=max(sizes), failures=bad[:10], ok=ok))


def macro_net(init, port_seqs, ctrl_u, Tmax):
    """One macrocell; ports and controls are forced vertices.
    init: bits of A, C, B, A', B'; port_seqs[X]: sequence; ctrl_u[X]: list of u."""
    net = Net(True)
    node = {X: net.add(b) for X, b in zip('ACBab', init)}
    net.link(node['A'], node['C']); net.link(node['C'], node['B'])
    net.link(node['A'], node['a']); net.link(node['B'], node['b'])
    for X in NODES:
        e = net.add(port_seqs[X][0]); net.link(node[X], e); net.forced.append((e, port_seqs[X]))
        for j in (1, 2):
            seq = [1 if j <= u else 0 for u in ctrl_u[X]]
            e = net.add(seq[0]); net.link(node[X], e); net.forced.append((e, seq))
    return net, [node[X] for X in 'ACBab']


def test_macrocell(build, report, rng, trials):
    """HOLD against arbitrary ports; RESET4 from any state with one port held
    at 0; LOAD_OR4 from quiescent 0 with constant ports; COPY = RESET4+LOAD4."""
    T = 40
    fails, cases, worst_reset, worst_load = [], 0, 0, 0

    def run(init, ports, u):
        nonlocal cases
        net, probes = macro_net(init, ports, u, T)
        info, hists = run_sim(net, T, probes, build)
        cases += 1
        return [list(h) for h in hists[0]]

    def settle(hs, r):
        return next((t for t in range(T + 1) if all(all(x == r for x in h[t:]) for h in hs)), 99)

    for b in (0, 1):                                    # HOLD
        for _ in range(trials):
            ports = {X: [rng.randrange(2) for _ in range(T + 1)] for X in NODES}
            if rng.random() < 0.3:
                ports = {X: [1 - b] * (T + 1) for X in NODES}
            hs = run([b] * 5, ports, {X: [1] * (T + 1) for X in NODES})
            if any(h != [b] * (T + 1) for h in hs):
                fails.append(('HOLD', b))
    for init in itertools.product((0, 1), repeat=5):   # RESET
        for zero in NODES:
            for _ in range(max(1, trials // 8)):
                ports = {X: [rng.randrange(2) for _ in range(T + 1)] for X in NODES}
                ports[zero] = [0] * (T + 1)
                hs = run(list(init), ports, {X: [0] * 4 + [1] * (T - 3) for X in NODES})
                worst_reset = max(worst_reset, settle(hs, 0))
                if any(h[4:] != [0] * (T - 3) for h in hs):
                    fails.append(('RESET', init, zero))
    for pv in itertools.product((0, 1), repeat=3):     # LOAD_OR
        ports = {X: [v] * (T + 1) for X, v in zip(NODES, pv)}
        hs = run([0] * 5, ports, {X: [2] * 4 + [1] * (T - 3) for X in NODES})
        r = int(any(pv))
        worst_load = max(worst_load, settle(hs, r))
        if any(h[4:] != [r] * (T - 3) for h in hs):
            fails.append(('LOAD_OR', pv))
    for init in itertools.product((0, 1), repeat=5):   # COPY with the source on any port
        for src in NODES:
            for v in (0, 1):
                ports = {X: [0] * (T + 1) for X in NODES}
                ports[src] = [v] * (T + 1)
                hs = run(list(init), ports, {X: [0] * 4 + [2] * 4 + [1] * (T - 7) for X in NODES})
                if any(h[8:] != [v] * (T - 7) for h in hs):
                    fails.append(('COPY', init, src, v))
    report.append(dict(test='macrocell modes (HOLD, RESET4, LOAD_OR4, COPY8), adversarial ports',
                       cases=cases, worst_reset_steps=worst_reset, worst_load_steps=worst_load,
                       failures=fails[:10], ok=not fails))


def test_costs5(report):
    bad = []
    for M in range(1, 10):
        for c in all_circuits(M) if M <= 3 else [random_circuit(M, random.Random(M), 2)]:
            steps, _, cost = program5(c)
            for (args, n) in cost.get('READ', ()):
                if n != 12 * args[0] + 44:
                    bad.append(('READ', args, n))
            for (args, n) in cost.get('GATE', ()):
                if n != 27:
                    bad.append(('GATE', n))
            for (args, n) in cost.get('WRITE', ()):
                if n != 12 * args[0] + 24:
                    bad.append(('WRITE', args, n))
            for (args, n) in cost.get('CLEAN', ()):
                if n != 8:
                    bad.append(('CLEAN', n))
            for (pqi, n) in cost.get('PER_GATE', ()):
                p, q, i = pqi
                if n != 12 * (p + q + i) + 147 or n > 36 * M + 147:
                    bad.append(('gate', pqi, n))
            L = len(steps)
            if L > 36 * M * M + 147 * M or L > 183 * M * M or L + 1 > 200 * M * M + 200:
                bad.append(('L', M, L))
    report.append(dict(test='program durations (COPY8 CLEAR4 MOVE12 STORE24 READ 12i+44 GATE27 WRITE 12i+24)',
                       failures=bad[:10], ok=not bad))


def run_reductions5(build, report, circuits, label, H_rule='spec', ever=(False, True),
                    controls='forced', compress=True, verbose=True):
    for c in circuits:
        for e in ever:
            red = Reduction5(c, ever=e)
            if H_rule == 'min':
                red = Reduction5(c, H=red.L + 1, ever=e)
            ref = None
            if controls == 'gen':
                _, ref = check5(red, build, True, 'forced')
            res, _ = check5(red, build, compress, controls, compare=ref)
            report.append(dict(test=label, **res))
            if verbose and not res['ok']:
                print(json.dumps(report[-1], default=str)[:2500], flush=True)


def test_mutations5(build, report, rng):
    circuits = [[('IN',), ('IN',), ('AND', 1, 2)], [('IN',), ('IN',), ('OR', 2, 1)],
                [('IN',), ('OR', 1, 1), ('AND', 2, 1)], [('IN',), ('IN',), ('AND', 2, 2)]]
    words = [tuple(rng.randrange(2) for _ in range(H + 1)) for H in (6, 9, 12, 20)]
    words += [tuple(t % 2 for t in range(17))]
    for m in ('reset3', 'load3', 'gate_no_phase4', 'gate_phase5_hold', 'pulse_no_shift'):
        MUT.clear(); MUT.add(m)
        detected, how = False, []
        try:
            _, info, bad, _, _ = gen_forest5(words, build, rng, True)
            if bad:
                detected = True; how.append('generator: %d failures' % len(bad))
            for c in circuits:
                res, _ = check5(Reduction5(c), build, True, 'forced')
                if not res['ok']:
                    detected = True
                    how.append('%s: %s' % (c, res['failures'][:1]))
        except ValueError as e:
            detected = True; how.append('construction refused: %s' % e)
        finally:
            MUT.clear()
        report.append(dict(test='mutation detected', mutation=m, detected=detected, how=how[:3],
                           ok=True))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--build', default=os.path.join(tempfile.gettempdir(), 'treered-build'))
    ap.add_argument('--out', default=None)
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--only', nargs='*', default=None)
    ap.add_argument('--seed', type=int, default=20261007)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    report = []
    t0 = time.time()
    heavy = {'full', 'm4', 'random'}

    def want(name):
        if args.only is not None:
            return name in args.only
        return not (args.quick and name in heavy)

    if want('costs'):
        test_costs5(report)
    if want('pulses'):
        test_pulses(args.build, report, rng, 16 if args.quick else 40)
    if want('generators'):
        test_generators5(args.build, report, rng, 6 if args.quick else 9,
                         [(16, 10, 'random', ALL_ADV), (20, 2, 'alternating', ('anti',))]
                         if args.quick else
                         [(16, 40, 'random', ALL_ADV), (16, 4, 'alternating', ALL_ADV),
                          (24, 10, 'random', ('anti', 'rand')), (24, 2, 'alternating', ('anti', 'rand')),
                          (24, 2, 'pairs', ('anti', 'rand')), (32, 4, 'random', ('anti',)),
                          (40, 1, 'alternating', ('anti',)), (48, 3, 'random', ('anti',)),
                          (64, 1, 'alternating', ('anti',)), (80, 1, 'pairs', ('anti',)),
                          (96, 1, 'random', ('anti',))])
    if want('macrocell'):
        test_macrocell(args.build, report, rng, 8 if args.quick else 40)
    if want('mutations'):
        test_mutations5(args.build, report, rng)
    if want('forced'):
        circ = [c for M in (1, 2, 3) for c in all_circuits(M)]
        run_reductions5(args.build, report, circ, 'macrocell program, all circuits M<=3, H=200M^2+200')
    if want('m4'):
        run_reductions5(args.build, report, all_circuits(4), 'macrocell program, all circuits M=4, H=200M^2+200')
    if want('random'):
        r2 = random.Random(args.seed + 1)
        circ = [random_circuit(M, r2, r2.randrange(1, 4)) for M in range(5, 13) for _ in range(4)]
        run_reductions5(args.build, report, circ, 'macrocell program, random circuits M=5..12')
    if want('full'):
        circ = [[('IN',)], [('IN',), ('AND', 1, 1)], [('IN',), ('OR', 1, 1)],
                [('IN',), ('IN',), ('AND', 1, 2)], [('IN',), ('IN',), ('OR', 2, 1)]]
        run_reductions5(args.build, report, circ, 'full tree (real generators), H = L+1',
                        H_rule='min', controls='gen')
    ok = all(r.get('ok') for r in report)
    summary = dict(ok=ok, tests=len(report), failed=[i for i, r in enumerate(report) if not r.get('ok')],
                   seconds=round(time.time() - t0, 1))
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(dict(summary=summary, report=report), f, indent=1, default=str)
    for r in report:
        brief = {k: r[k] for k in r if k in ('test', 'H', 'M', 'compress', 'controls', 'kind', 'cases',
                                              'words', 'n', 'stored_vertices', 'tree_vertices',
                                              'mutation', 'detected', 'worst_reset_steps',
                                              'worst_load_steps', 'ok', 'n_failures', 'seconds')}
        print(json.dumps(brief, default=str))
    print(json.dumps(summary))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
