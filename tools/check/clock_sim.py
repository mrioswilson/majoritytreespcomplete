#!/usr/bin/env python3
"""Explicit construction and simulation of the robust generators.

Builds, exactly as described in the paper, the constant sources, the timers
D_h and U_h (Lemma on timers), the pulses P_{a,b}, and the phase-defect
generators (combiner recursion, bases K = 0, 1, 2).  Each tree is simulated
with plain synchronous majority (ties keep the state) against several
consumer strategies, including adaptive adversaries that see the whole
current configuration.  Checks:

  * root history equals the prescribed word for every strategy;
  * the tree is a simple tree; all degrees (consumer edge included) lie in
    {1, 3, 4}; timers and pulses use only degrees 1 and 3;
  * timer sizes are 8h - 1 (h >= 1) and 7 (h = 0);
  * the logspace counting recurrence (5) reproduces the defect sets of the
    recursion at every skeleton node;
  * the word characterisation (6);
  * the finite-window reader, with real pulse generators.

A sanity check of the written proofs, not a substitute for them.
"""
import itertools
import random
import sys

sys.setrecursionlimit(100000)


class Tree:
    def __init__(self):
        self.bit = []
        self.adj = []

    def v(self, b):
        self.bit.append(b & 1)
        self.adj.append([])
        return len(self.bit) - 1

    def e(self, u, w):
        self.adj[u].append(w)
        self.adj[w].append(u)


def const(T, c):
    r = T.v(c)
    for _ in range(2):
        T.e(r, T.v(c))
    return r


def timer(T, h):
    """D_h(t) = 1{t < h}."""
    if h == 0:
        r = T.v(0)
        T.e(r, const(T, 0))
        T.e(r, const(T, 0))
        return r
    r = T.v(1)
    L = h - 1
    if L == 0:
        T.e(r, const(T, 0))
        T.e(r, const(T, 0))
        return r
    for _ in range(2):
        parent = r
        for k in range(L - 1, -1, -1):        # head first, bottom last
            x = T.v(1)
            T.e(parent, x)
            if k == 0:
                T.e(x, const(T, 0))
                T.e(x, const(T, 0))
            else:
                T.e(x, const(T, 0))
            parent = x
    return r


def pulse(T, a, b):
    """P_{a,b}(t) = 1{a <= t < b}, 0 <= a < b."""
    assert 0 <= a < b
    if a == 0:
        return timer(T, b)
    B, L = b - a, a - 1
    r = T.v(0)
    if L == 0:
        T.e(r, timer(T, B))
        T.e(r, timer(T, B))
        return r
    for _ in range(2):
        chain = []
        parent = r
        for k in range(L - 1, -1, -1):
            x = T.v(0)
            T.e(parent, x)
            chain.append((k, x))
            parent = x
        for k, x in chain:
            if k == 0:
                T.e(x, timer(T, B))
                T.e(x, timer(T, B))
            else:
                T.e(x, timer(T, B + k))
    return r


def parity_transform(T, root, first, beta):
    """Complement initial bits where chi(v) XOR beta = 1 on the subtree built
    in vertex range [first, len)."""
    dist = {root: 0}
    stack = [root]
    while stack:
        u = stack.pop()
        for w in T.adj[u]:
            if w >= first and w not in dist:
                dist[w] = dist[u] + 1
                stack.append(w)
    assert len(dist) == len(T.bit) - first
    for v, d in dist.items():
        if (d & 1) ^ beta:
            T.bit[v] ^= 1


def children_sets(D):
    E = sorted(x for x in D if x != 0)
    return [sorted(a - 1 for r, a in enumerate(E) if r % 3 != j) for j in range(3)]


def gen(T, D, beta, skeleton=None, addr=()):
    D = sorted(D)
    K = len(D)
    if skeleton is not None:
        skeleton[addr] = D
    if K == 0:
        r = T.v(beta)
        T.e(r, T.v(1 - beta))
        T.e(r, T.v(1 - beta))
        return r
    if K == 1:
        a = D[0]
        first = len(T.bit)
        r = pulse(T, a, a + 1)
        parity_transform(T, r, first, beta)
        return r
    r = T.v(beta ^ (1 if 0 in D else 0))
    for j, Dj in enumerate(children_sets(D)):
        T.e(r, gen(T, Dj, 1 - beta, skeleton, addr + (j,)))
    return r


def simulate(T, root, steps, strategy, target, rng):
    n = len(T.bit)
    x = list(T.bit)
    hist = []
    for t in range(steps):
        hist.append(x[root])
        if strategy == 'zero':
            cons = 0
        elif strategy == 'one':
            cons = 1
        elif strategy == 'random':
            cons = rng.randint(0, 1)
        elif strategy == 'adversary':        # votes against the next bit
            cons = 1 - target(t + 1)
        elif strategy == 'mirror':           # feedback: copies the root
            cons = x[root]
        elif strategy == 'antimirror':
            cons = 1 - x[root]
        new = [0] * n
        for v in range(n):
            nb = T.adj[v]
            s = sum(x[u] for u in nb)
            d = len(nb)
            if v == root:
                s += cons
                d += 1
            if 2 * s > d:
                new[v] = 1
            elif 2 * s < d:
                new[v] = 0
            else:
                new[v] = x[v]
        x = new
    return hist


def check_tree(T, root, allowed):
    n = len(T.bit)
    m = sum(len(a) for a in T.adj) // 2
    assert m == n - 1, 'not a tree (edge count)'
    seen = {root}
    stack = [root]
    while stack:
        u = stack.pop()
        for w in T.adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    assert len(seen) == n, 'not connected'
    for v in range(n):
        d = len(T.adj[v]) + (1 if v == root else 0)
        assert d in allowed, ('degree', v, d)


STRATS = ['zero', 'one', 'random', 'adversary', 'mirror', 'antimirror']


def test_timers_pulses(rng):
    for h in range(0, 30):
        T = Tree()
        r = timer(T, h)
        check_tree(T, r, {1, 3})
        assert len(T.bit) == (8 * h - 1 if h >= 1 else 7)
        for s in STRATS:
            tgt = lambda t, h=h: 1 if t < h else 0
            assert simulate(T, r, h + 6, s, tgt, rng) == [tgt(t) for t in range(h + 6)]
    for a in range(0, 16):
        for b in range(a + 1, 20):
            T = Tree()
            r = pulse(T, a, b)
            check_tree(T, r, {1, 3})
            tgt = lambda t, a=a, b=b: 1 if a <= t < b else 0
            for s in STRATS:
                assert simulate(T, r, b + 5, s, tgt, rng) == [tgt(t) for t in range(b + 5)]
    print('timers h<30 and pulses a<16, b<20: OK')


def no_consec_sets(Hmax):
    for H in range(Hmax + 1):
        for bits in itertools.product((0, 1), repeat=H + 1):
            if any(bits[i] and bits[i + 1] for i in range(H)):
                continue
            if H > 0 and not bits[H]:
                continue                      # enumerate each set once
            yield H, [t for t in range(H + 1) if bits[t]]


def F(j, u):
    return u - (u + 2 - j) // 3


def check_counting(D, skeleton, H):
    """Recurrence (5) via the procedure of the logspace enumeration."""
    def Q_root(t):
        return sum(1 for x in D if x <= t) if t >= 0 else 0
    for addr, Dp in skeleton.items():
        d = len(addr)
        # zero-event bits sigma_1..sigma_d of the prefixes (sigma_1 = root)
        sig = []
        for ell in range(1, d + 1):
            u = Q_root(ell - 1)
            for r in range(1, ell):
                u = F(addr[r - 1], u - sig[r - 1])
            sig.append(u)
        for t in range(-1, H + 1):
            if t < 0:
                q = 0
            else:
                u = Q_root(t + d)
                for r in range(1, d + 1):
                    u = F(addr[r - 1], u - sig[r - 1])
                q = u
            assert q == sum(1 for x in Dp if x <= t), (D, addr, t)
        u = len(D)
        for r in range(1, d + 1):
            u = F(addr[r - 1], u - sig[r - 1])
        assert u == len(Dp)


def test_generators(rng, Hmax):
    count = 0
    maxsize = 0
    for H, D in no_consec_sets(Hmax):
        for beta in (0, 1):
            T = Tree()
            sk = {}
            r = gen(T, D, beta, sk)
            check_tree(T, r, {1, 3, 4})
            check_counting(D, sk, H)
            tgt = lambda t, D=set(D), beta=beta: beta ^ (t & 1) ^ (1 if t in D else 0)
            want = [tgt(t) for t in range(H + 8)]
            for s in STRATS:
                assert simulate(T, r, H + 8, s, tgt, rng) == want, (D, beta, s)
            count += 1
            maxsize = max(maxsize, len(T.bit))
    print('phase-defect generators, all sets with max <= %d, both phases: %d OK '
          '(largest tree %d vertices)' % (Hmax, count, maxsize))


def test_random_large(rng, trials):
    for _ in range(trials):
        H = rng.randint(15, 26)
        D = []
        t = 0
        while t <= H:
            if rng.random() < 0.45:
                D.append(t)
                t += 2
            else:
                t += 1
        beta = rng.randint(0, 1)
        T = Tree()
        sk = {}
        r = gen(T, D, beta, sk)
        check_tree(T, r, {1, 3, 4})
        check_counting(D, sk, H)
        tgt = lambda t, D=set(D), beta=beta: beta ^ (t & 1) ^ (1 if t in D else 0)
        for s in ('random', 'adversary', 'mirror'):
            assert simulate(T, r, H + 6, s, tgt, rng) == [tgt(t) for t in range(H + 6)]
    print('random larger defect sets (H <= 26): %d OK' % trials)


def test_characterisation(rng):
    for H in range(0, 13):
        for w in itertools.product((0, 1), repeat=H + 1):
            for beta in (0, 1):
                D = [t for t in range(H + 1) if w[t] != beta ^ (t & 1)]
                noc = not any(D[i + 1] == D[i] + 1 for i in range(len(D) - 1))
                rule = all(w[s] == w[s - 1] or w[s] == beta ^ (s & 1)
                           for s in range(1, H + 1))
                assert noc == rule
    print('characterisation (6): all words of length <= 13 OK')


def test_reader(rng):
    for Tw in range(0, 12):
        for d in (0, 1):
            for trial in range(40):
                T = Tree()
                z = T.v(0)
                leaf = T.v(0)
                T.e(z, leaf)
                T.e(z, pulse(T, Tw, Tw + 2))
                T.e(z, pulse(T, Tw, Tw + 2))
                # z also has the input port q (external), degree 4
                n = len(T.bit)
                x = list(T.bit)
                seen1 = False
                for t in range(Tw + 25):
                    qv = d if t in (Tw, Tw + 1) else rng.randint(0, 1)
                    if trial % 3 == 0 and t not in (Tw, Tw + 1):
                        qv = 1                  # hostile: port 1 outside window
                    new = [0] * n
                    for v in range(n):
                        nb = T.adj[v]
                        s = sum(x[u] for u in nb)
                        deg = len(nb)
                        if v == z:
                            s += qv
                            deg += 1
                        new[v] = 1 if 2 * s > deg else (0 if 2 * s < deg else x[v])
                    x = new
                    if x[z]:
                        seen1 = True
                        assert t + 1 >= Tw + 1
                assert seen1 == (d == 1)
    print('finite-window reader with real pulses: OK')


def main():
    rng = random.Random(7)
    test_timers_pulses(rng)
    test_characterisation(rng)
    test_generators(rng, int(sys.argv[1]) if len(sys.argv) > 1 else 13)
    test_random_large(rng, 25)
    test_reader(rng)
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
