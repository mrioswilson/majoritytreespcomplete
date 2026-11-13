#!/usr/bin/env python3
"""Reference data for tools/test_model.cjs, from the verified Python
implementation of the degree-5 construction (tools/generator/deg5.py, a copy of
research/degree5-check-20261007/deg5.py; see tools/generator/PROVENANCE.sha256).

For words: the structure of the generator (fingerprint) and its plain size.
For circuits: L, H, S, T, checkpoints, every control history, the size of the
full tree, and a hash of the exact history of every macrocell vertex (and z)
for every input assignment, from a direct simulation of the majority rule.
"""
import argparse
import hashlib
import itertools
import json
import os
import random
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'generator'))
import treered as tr  # noqa: E402
import deg5  # noqa: E402


def fingerprint(h):
    """Structure of the degree-5 generator of history h."""
    K = h.K
    if K == 0:
        return 'C%d' % h.b0
    if K == 1:
        return ('U' if h.b0 == 0 else 'D') + str(h.ch[0])
    if K == 2:
        return ('~' if h.b0 == 1 else '') + 'P[%d,%d)' % h.ch
    return 'N(' + ','.join(fingerprint(h.child(j)) for j in range(4)) + ')'


def plain_size(h):
    net = tr.Net(True)
    return deg5.generator5(net, h)[2]


def circuits(rng):
    out = [c for M in (1, 2, 3) for c in tr.all_circuits(M)]
    out += [c for c in tr.all_circuits(4)][::23]
    out += [tr.random_circuit(M, rng, rng.randrange(1, 4)) for M in (5, 6, 7, 8)]
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default=os.path.join(HERE, 'reference.json'))
    ap.add_argument('--build', default=os.path.join(tempfile.gettempdir(), 'trees-site-build'))
    args = ap.parse_args()
    rng = random.Random(20261007)
    words = []
    for H in range(1, 9):
        for x in range(2 ** (H + 1)):
            words.append([int(c) for c in format(x, '0%db' % (H + 1))])
    for H in (16, 24, 40, 64):
        for _ in range(6):
            words.append([rng.randrange(2) for _ in range(H + 1)])
        b = rng.randrange(2)
        words.append([(b + t) % 2 for t in range(H + 1)])
    ref = {'words': [], 'circuits': []}
    sizes = {}
    for w in words:
        h = tr.word_hist(tuple(w))
        ref['words'].append({'w': ''.join(map(str, w)), 'fp': fingerprint(h), 'size': plain_size(h)})
    for c in circuits(rng):
        for ever in (False, True):
            red = deg5.Reduction5(c, ever=ever)
            controls, size = [], 0
            for v in red.names:
                size += 5
                for xi in range(3):
                    us = [red.u(v, xi, i) for i in range(red.H + 1)]
                    for j in (1, 2):
                        h = tr.word_hist(tuple(1 if j <= x else 0 for x in us))
                        controls.append([h.b0] + list(h.ch))
                        key = (h.b0, h.ch)
                        if key not in sizes:
                            sizes[key] = plain_size(h)
                        size += sizes[key]
            used = set()
            for a, b in red.edges:
                used.add((a, red.port[(a, b)])); used.add((b, red.port[(b, a)]))
            if ever:
                used.add((red.out, 'B'))
                size += 2 + 8 * (red.T + 1) - 1
            size += 3 * sum(1 for v in red.names for X in 'ACB' if (v, X) not in used)
            res, hist = deg5.check5(red, args.build, True, 'forced')
            if not res['ok']:
                raise SystemExit('reference run failed: %s' % res['failures'][:3])
            macro = []
            assignments = list(itertools.product((0, 1), repeat=len(red.inputs)))
            for bits, by in zip(assignments, hist):
                d = hashlib.sha256()
                for v in red.names:
                    for X in 'ACBab':
                        d.update(bytes(by[(v, X)]))
                macro.append({'bits': list(bits), 'cells': d.hexdigest()})
            ref['circuits'].append({
                'nodes': [list(n) for n in red.circuit], 'ever': ever, 'L': red.L, 'H': red.H, 'S': red.S,
                'T': red.T, 'checkpoints': [list(cp) for cp in red.checkpoints], 'size': size,
                'controls': hashlib.sha256(json.dumps(controls, separators=(',', ':')).encode()).hexdigest(),
                'macro': macro})
    with open(args.out, 'w') as f:
        json.dump(ref, f)
    print('words %d, circuit runs %d -> %s' % (len(ref['words']), len(ref['circuits']), args.out))


if __name__ == '__main__':
    main()
