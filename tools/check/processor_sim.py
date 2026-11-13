#!/usr/bin/env python3
"""Vertex-level check of the degree-four serial tree processor.

This script re-implements, from the text of the manuscript, the processor of
Sections 5 and 8 (in the consolidated paper: Sections 5-7 and 9) with every
control vertex FORCED to its scheduled word.  By the substitution principle
(robust generators), this is exactly what the processor vertices see in the
closed tree on [0, H].

Checks performed for every simulated instance:
  * every vertex follows plain synchronous majority (ties keep the state),
    with the two cell controls encoded as HOLD=(0,1), RESET=(0,0), LOAD=(1,1);
  * NORMAL(c) holds exactly, with the expected register contents, at the end
    of every instruction (and is re-checked one step later for stability);
  * the designated register holds the program's value at the query time;
  * every control word satisfies the phase condition (6) for its fixed phase:
        w(s) != w(s-1)  ==>  w(s) == beta XOR (s mod 2);
  * no cell receives two overlapping mode assignments;
  * the instruction lengths agree with the closed formula of the paper;
  * the EVER variant (reader z replacing the far clock of R_m, final write
    without restoration) satisfies: z ever 1  <=>  output 1, with z = 0
    before tau + 1, under arbitrary later behaviour of R_m.

It is a sanity check of the written proof, not a substitute for it.
"""
import itertools
import random
import sys

R, H_, L = 'R', 'H', 'L'
CTRL = {R: (0, 0), H_: (0, 1), L: (1, 1)}


def maj(*xs):
    s = sum(xs)
    return 1 if 2 * s > len(xs) else 0


class Processor:
    def __init__(self, m, init_regs, ever=False):
        self.m = m
        self.ever = ever
        self.cells = {}        # name -> (end0, end1)
        self.adj = {}          # vertex -> list of neighbours (data only)
        self.partner = {}
        self.cell_of = {}
        self.junctions = []
        self.ports = {}        # forced external vertices (far clocks)
        self.phase = {}        # control name -> phase
        self.state = {}
        self._build()
        # initial configuration NORMAL(0)
        c, b = 0, 1
        for i in range(m + 1):
            self._setcell('E%d' % i, c)
        for i in range(1, m + 1):
            self._setcell('C%d' % i, b)
            self._setcell('K%d' % i, b)
            self._setcell('R%d' % i, init_regs[i])
            self.state['r%d' % i] = c
        for x in 'AB':
            for nm in ('F', 'K', 'Q'):
                self._setcell(nm + x, b)
        self.state['G'] = c
        # schedules
        self.mode = {X: {} for X in self.cells}
        self.hrest = {g: [(0, 0)] for g in self.junctions}
        self.hover = {g: {} for g in self.junctions}
        self.farrest = {k: [(0, 1)] for k in self.ports}
        self.T = 0
        self.c = 0
        self.waits = []

    # ---------------------------------------------------------- topology
    def _cell(self, name, phase):
        a, b = name + '.0', name + '.1'
        self.cells[name] = (a, b)
        self.partner[a], self.partner[b] = b, a
        self.cell_of[a] = self.cell_of[b] = name
        self.adj.setdefault(a, [])
        self.adj.setdefault(b, [])
        self.phase['cell:' + name] = phase

    def _edge(self, u, v):
        self.adj.setdefault(u, []).append(v)
        self.adj.setdefault(v, []).append(u)

    def _build(self):
        m = self.m
        q = 0
        for i in range(m + 1):
            self._cell('E%d' % i, q)
        for i in range(1, m + 1):
            self._cell('C%d' % i, q)
            self._cell('K%d' % i, 1 - q)
            self._cell('R%d' % i, q)
        for x in 'AB':
            self._cell('F' + x, q)
            self._cell('K' + x, 1 - q)
            self._cell('Q' + x, q)
        self.junctions = ['G'] + ['r%d' % i for i in range(1, m + 1)]
        for g in self.junctions:
            self.adj[g] = []
            self.phase['h:' + g] = 1 - q
        # bus
        self._edge('G', 'E0.0')
        for i in range(1, m + 1):
            self._edge('E%d.1' % (i - 1), 'r%d' % i)
            self._edge('r%d' % i, 'E%d.0' % i)
            self._edge('r%d' % i, 'C%d.0' % i)
            self._edge('C%d.1' % i, 'K%d.0' % i)
            self._edge('K%d.1' % i, 'R%d.0' % i)
            self.ports['kappa%d' % i] = 'R%d.1' % i
        self.ports['kappa_end'] = 'E%d.1' % m
        for x in 'AB':
            self._edge('G', 'F%s.0' % x)
            self._edge('F%s.1' % x, 'K%s.0' % x)
            self._edge('K%s.1' % x, 'Q%s.0' % x)
            self.ports['kappa' + x] = 'Q%s.1' % x
        for k in self.ports:
            self.phase['far:' + k] = q
        if self.ever:
            del self.ports['kappa%d' % m]
            del self.phase['far:kappa%d' % m]
        # degree check of processor vertices (+2 controls per endpoint,
        # +1 control per junction, +1 port for far-clocked endpoints)
        portv = {v: k for k, v in self.ports.items()}
        if self.ever:
            portv['R%d.1' % m] = 'z'
        for v, nb in self.adj.items():
            if v in self.junctions:
                assert len(nb) == 3, (v, nb)
            else:
                deg = 1 + len(nb) + 2 + (1 if v in portv else 0)
                assert deg == 4, (v, nb, deg)

    def _setcell(self, X, x):
        a, b = self.cells[X]
        self.state[a] = self.state[b] = x

    # ---------------------------------------------------------- schedule
    def favor(self, X, z, t0, n):
        md = L if z == 1 else R
        for t in range(t0, t0 + n):
            assert t not in self.mode[X], ('mode clash', X, t)
            self.mode[X][t] = md

    def seth(self, g, t0, t1, v):
        for t in range(t0, t1):
            assert t not in self.hover[g], ('h clash', g, t)
            self.hover[g][t] = v

    def align(self, parity, tag):
        if self.T % 2 != parity:
            self.T += 1
            self.waits.append(tag)

    def route(self, g, A, B):
        c, b, T = self.c, 1 - self.c, self.T
        self.favor(A, c, T, 3)
        self.seth(g, T, T + 3, b)
        self.favor(B, b, T + 3, 3)
        self.T += 6

    def read(self, g, A, B, C, K, Rg):
        c, b, T = self.c, 1 - self.c, self.T
        self.seth(g, T, T + 11, b)
        self.favor(K, c, T + 1, 3)
        self.favor(K, b, T + 4, 3)
        self.favor(C, c, T + 4, 3)
        self.favor(A, c, T + 8, 3)
        self.favor(A, b, T + 11, 3)
        self.favor(C, b, T + 11, 3)
        self.T += 14

    def gate(self, g, A, B, C):
        c, b, T = self.c, 1 - self.c, self.T
        self.favor(C, b, T, 5)
        self.favor(A, c, T + 1, 3)
        self.favor(B, c, T + 1, 3)
        self.seth(g, T + 1, T + 4, b)
        self.T += 5

    def move(self, X, Y, z):
        self.favor(X, z, self.T, 3)
        self.favor(Y, 1 - z, self.T, 3)
        self.T += 3

    def sets(self, cells_z):
        for X, z in cells_z:
            self.favor(X, z, self.T, 3)
        self.T += 3

    # ---------------------------------------------------------- macro-ops
    def normalize(self):
        m, c = self.m, self.c
        b = 1 - c
        p = c
        self.align(p, 'norm')
        self.sets([('FA', c)])
        assert self.T % 2 == 1 - p
        self.sets([('E%d' % m, b)])          # COPY kappa_end = b into E_m
        t0 = self.T
        assert t0 % 2 == p
        for k in self.farrest:
            self.farrest[k].append((t0, c))
        for j in range(m, 0, -1):
            tj = t0 + 4 * (m - j)
            self.favor('C%d' % j, c, tj, 3)
            self.hrest['r%d' % j].append((tj, b))
            self.favor('K%d' % j, c, tj + 1, 3)
            self.favor('E%d' % (j - 1), b, tj + 1, 3)
        s = t0 + 4 * m
        for X in ('FA', 'FB', 'QA', 'QB'):
            self.favor(X, c, s, 3)
        self.hrest['G'].append((s, b))
        self.favor('KA', c, s + 1, 3)
        self.favor('KB', c, s + 1, 3)
        self.T = s + 4
        self.c = b

    def fetch(self, i, F, KF):
        c = self.c
        t_start = self.T
        self.route('G', F, 'E0')
        self.T += 1                                   # internal wait
        self.sets([(KF, c)])
        for j in range(1, i):
            self.route('r%d' % j, 'E%d' % (j - 1), 'E%d' % j)
        self.read('r%d' % i, 'E%d' % (i - 1), 'E%d' % i,
                  'C%d' % i, 'K%d' % i, 'R%d' % i)
        for j in range(i - 1, 0, -1):
            self.route('r%d' % j, 'E%d' % j, 'E%d' % (j - 1))
        self.route('G', 'E0', F)
        assert self.T - t_start == 12 * i + 18

    def instruction(self, k, op, i, j, final_ever=False):
        m = self.m
        cneed = 0 if op == 'AND' else 1
        if cneed != self.c:
            self.normalize()
        c = self.c
        b = 1 - c
        p = c
        t_begin = self.T
        # 1. prepare
        self.align(p, 'prep')
        if final_ever:
            self.sets([('C%d' % k, c)])
            self.sets([('K%d' % k, c)])
        else:
            self.sets([('C%d' % k, c)])
            self.sets([('K%d' % k, c), ('R%d' % k, b)])
        # 2. fetch i, store
        self.align(p, 'fetch1')
        self.fetch(i, 'FA', 'KA')
        self.align(p, 'store')
        self.sets([('KA', b)])
        self.move('FA', 'KA', b)
        self.move('KA', 'QA', b)
        # 3. fetch j, recover
        self.align(p, 'fetch2')
        self.fetch(j, 'FB', 'KB')
        self.align(1 - p, 'recover')
        self.sets([('KA', c)])        # COPY_b from QA into KA
        self.sets([('FA', c)])
        self.move('KA', 'FA', c)
        # 4. gate
        self.align(1 - p, 'gate')
        self.gate('G', 'FA', 'FB', 'E0')
        # 5. clean temporaries and buffers
        self.align(1 - p, 'clean')
        self.sets([('QA', b), ('QB', b)])
        self.sets([('KA', b), ('KB', b)])
        # 6. writing routes
        self.align(p, 'left')
        for jj in range(1, k):
            self.route('r%d' % jj, 'E%d' % (jj - 1), 'E%d' % jj)
        self.align(1 - p, 'pilot')
        self.sets([('E%d' % m, b)])   # COPY kappa_end into E_m
        self.align(p, 'right')
        for jj in range(m, k, -1):
            self.route('r%d' % jj, 'E%d' % jj, 'E%d' % (jj - 1))
        if final_ever:
            self.align(0, 'final')
            self.route('r%d' % k, 'E%d' % (k - 1), 'C%d' % k)
            self.move('C%d' % k, 'K%d' % k, 0)
            self.move('K%d' % k, 'R%d' % k, 0)
            return self.T - t_begin
        # 7. commit
        self.align(p, 'commit')
        T = self.T
        self.route('r%d' % k, 'E%d' % (k - 1), 'C%d' % k)
        self.sets([('K%d' % k, b)])
        self.move('C%d' % k, 'K%d' % k, b)
        self.favor('E%d' % k, c, self.T, 3)
        self.move('K%d' % k, 'R%d' % k, b)
        assert self.T - T == 15
        # 8. fronts
        self.align(1 - p, 'fronts')
        self.sets([('FA', b), ('FB', b)])
        return self.T - t_begin

    # ---------------------------------------------------------- words
    def h_at(self, g, t):
        if t in self.hover[g]:
            return self.hover[g][t]
        v = None
        for (s, val) in self.hrest[g]:
            if s <= t:
                v = val
        return v

    def far_at(self, k, t):
        v = None
        for (s, val) in self.farrest[k]:
            if s <= t:
                v = val
        return v

    def words(self, Hz):
        W = {}
        for X in self.cells:
            md = [self.mode[X].get(t, H_) for t in range(Hz + 1)]
            W['cell:%s#1' % X] = ([CTRL[x][0] for x in md], self.phase['cell:' + X])
            W['cell:%s#2' % X] = ([CTRL[x][1] for x in md], self.phase['cell:' + X])
        for g in self.junctions:
            W['h:' + g] = ([self.h_at(g, t) for t in range(Hz + 1)], self.phase['h:' + g])
        for k in self.ports:
            W['far:' + k] = ([self.far_at(k, t) for t in range(Hz + 1)], self.phase['far:' + k])
        return W

    # ---------------------------------------------------------- dynamics
    def step(self, t, extra_port=None):
        st = self.state
        new = {}
        portval = {v: self.far_at(k, t) for k, v in self.ports.items()}
        if extra_port:
            portval.update(extra_port)
        for X, (a, b_) in self.cells.items():
            c1, c2 = CTRL[self.mode[X].get(t, H_)]
            for v in (a, b_):
                nb = self.adj[v]
                if nb:
                    d = st[nb[0]]
                else:
                    d = portval[v]
                new[v] = maj(st[v], st[self.partner[v]], d, c1, c2)
        for g in self.junctions:
            nb = self.adj[g]
            new[g] = maj(st[g], st[nb[0]], st[nb[1]], st[nb[2]], self.h_at(g, t))
        self.state = new


def check_phase(word, beta):
    for s in range(1, len(word)):
        if word[s] != word[s - 1] and word[s] != (beta ^ (s & 1)):
            return s
    return None


def uniform(st, cells, X):
    a, b = cells[X]
    return st[a] if st[a] == st[b] else None


def check_normal(P, c, regs, label):
    b = 1 - c
    st, m = P.state, P.m
    errs = []
    for i in range(m + 1):
        if uniform(st, P.cells, 'E%d' % i) != c:
            errs.append('E%d' % i)
    for i in range(1, m + 1):
        if st['r%d' % i] != c:
            errs.append('r%d' % i)
        for X in ('C%d' % i, 'K%d' % i):
            if uniform(st, P.cells, X) != b:
                errs.append(X)
        if regs[i] is not None and uniform(st, P.cells, 'R%d' % i) != regs[i]:
            errs.append('R%d' % i)
    if st['G'] != c:
        errs.append('G')
    for X in ('FA', 'KA', 'QA', 'FB', 'KB', 'QB'):
        if uniform(st, P.cells, X) != b:
            errs.append(X)
    if errs:
        raise AssertionError('NORMAL(%d) fails at %s: %s' % (c, label, errs))


def run(circuit, ever=False, check_words=True, rng=None):
    """circuit: list of nodes 1..m: ('C', v) or ('AND'|'OR', i, j).
    The last node must be AND(o, o) (the appended final gate)."""
    m = len(circuit)
    val = [None] * (m + 1)
    for k, node in enumerate(circuit, 1):
        if node[0] == 'C':
            val[k] = node[1]
        else:
            x, y = val[node[1]], val[node[2]]
            val[k] = (x & y) if node[0] == 'AND' else (x | y)
    init = [None] + [(node[1] if node[0] == 'C' else 0) for node in circuit]
    P = Processor(m, init, ever=ever)
    # build the whole schedule first
    marks = []
    for k, node in enumerate(circuit, 1):
        if node[0] == 'C':
            continue
        final = ever and k == m
        renorm = (0 if node[0] == 'AND' else 1) != P.c
        T0 = P.T
        d = P.instruction(k, node[0], node[1], node[2], final_ever=final)
        if not final:
            i, j = node[1], node[2]
            expect = 12 * (i + j) + 6 * m + 92
            got = P.T - T0 - (4 * m + 11 if renorm else 0)
            assert got == expect, (k, got, expect)
        marks.append((P.T, k, P.c, final))
    tau = P.T
    Hz = tau + 6
    if check_words:
        for name, (w, beta) in P.words(Hz).items():
            s = check_phase(w, beta)
            assert s is None, ('phase (6) violated', name, s)
    # simulate
    regs = [None] * (m + 1)
    for k, node in enumerate(circuit, 1):
        if node[0] == 'C':
            regs[k] = node[1]
    # EVER reader: z adjacent to R_m.1, leaf l, two pulses P_{tau,tau+2}
    z = l = 0
    zhist = []
    mi = 0
    after = None
    for t in range(Hz):
        extra = None
        if ever:
            extra = {'R%d.1' % m: z}
        if ever and t >= tau + 2 and rng is not None:
            # after the window the processor may misbehave arbitrarily:
            # perturb R_m's far endpoint at random to stress the reader
            P.state['R%d.1' % m] = rng.randint(0, 1)
        qv = P.state['R%d.1' % m]
        P.step(t, extra)
        if ever:
            pulse = 1 if tau <= t < tau + 2 else 0
            z, l = maj(z, qv, l, pulse, pulse), z
            zhist.append(z)
        while mi < len(marks) and marks[mi][0] == t + 1:
            T, k, c, final = marks[mi]
            if not final:
                regs[k] = val[k]
                check_normal(P, c, regs, 'after instruction %d' % k)
            mi += 1
        if t + 1 == tau:
            a, b_ = P.cells['R%d' % m]
            assert P.state[a] == P.state[b_] == val[m], ('output', val[m])
            after = True
    assert after
    if ever:
        assert all(v == 0 for v in zhist[:tau]), 'z rose before the window'
        assert (1 in zhist) == (val[m] == 1), ('reader', val[m], zhist[tau - 1:tau + 4])
    return tau, P


def random_circuit(rng, nodes):
    circ = [('C', rng.randint(0, 1))]
    for k in range(2, nodes + 1):
        r = rng.random()
        if r < 0.2:
            circ.append(('C', rng.randint(0, 1)))
        else:
            op = 'AND' if rng.random() < 0.5 else 'OR'
            circ.append((op, rng.randint(1, k - 1), rng.randint(1, k - 1)))
    o = len(circ)
    circ.append(('AND', o, o))
    return circ


def all_circuits(nodes):
    def opts(k):
        out = [('C', 0), ('C', 1)]
        for op in ('AND', 'OR'):
            for i in range(1, k):
                for j in range(1, k):
                    out.append((op, i, j))
        return out
    for combo in itertools.product(*[opts(k) for k in range(1, nodes + 1)]):
        if combo[0][0] != 'C':
            continue
        circ = list(combo)
        circ.append(('AND', nodes, nodes))
        yield circ


def main():
    rng = random.Random(20261113)
    n = 0
    for nodes in (1, 2, 3):
        for circ in all_circuits(nodes):
            run(circ)
            run(circ, ever=True, rng=rng)
            n += 1
    print('exhaustive circuits with <= 3 source nodes (+ final AND):', n)
    taus = []
    for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 60):
        nodes = rng.randint(4, 9)
        circ = random_circuit(rng, nodes)
        tau, _ = run(circ)
        run(circ, ever=True, rng=rng)
        m = len(circ)
        taus.append((m, tau))
        assert tau <= 10000 * (m + 1) ** 2
    print('random circuits:', len(taus), ' max m:', max(m for m, _ in taus))
    worst = max(t / (m + 1) ** 2 for m, t in taus)
    print('max tau/(m+1)^2 observed: %.1f' % worst)
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
