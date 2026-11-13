/* majsim.c - synchronous majority dynamics (each vertex takes the majority
 * of its neighbours; a tie keeps the current state) on a tree given as
 * weighted arcs.  Used by treered.py to test the reduction of
 * research/majority-treewidth-deepen-20261006 by direct simulation.
 *
 * An arc u->v with weight k means that u counts the state of v k times.
 * treered.py writes links in pairs (parent->child weight k, child->parent
 * weight 1).  k > 1 encodes k identical private subtrees hanging from the
 * same vertex: identical copies with identical initial states see the same
 * outside world and therefore evolve identically, so one stored copy with
 * multiplicity k is an exact encoding.  With compress = 0 every weight is 1
 * and the arcs describe the plain tree.
 *
 * Timer macros (hardness.txt section 3) are expanded here:
 *   port r, two identical arms r - v1 - ... - vL - a, L = tau - 1;
 *   every v_i carries a constant cherry (root + two leaves), a is the root
 *   of another cherry.  Rising: arms 0, cherries 1.  Falling: complement.
 *
 * Input (little endian):
 *   "MAJ2", int32 compress,
 *   int64 n0, a0, ntim, nforced, nprobes, nsets, nover, Tmax
 *   uint8 state[n0]
 *   int32 timer[3*ntim]   (port, tau, rising)
 *   int32 au[a0], int32 av[a0], uint8 aw[a0]
 *   int32 fv[nforced], uint8 fbits[nforced*(Tmax+1)]
 *   int32 pv[nprobes]
 *   int32 ov[nover], uint8 obits[nsets*nover]
 * A forced vertex takes fbits[t] at every time t (adversarial consumer).
 * Override set s replaces the initial state of ov[i] by obits[s*nover+i].
 * Output file: for each set, uint8 hist[nprobes*(Tmax+1)].
 * Standard output: one JSON line with structural checks and timing.
 * With MAJSIM_TRANSIENT=1 it also reports, for each set, the stabilisation
 * time min{t : x(t+2) = x(t) at every vertex} (-1 if not reached by Tmax).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static void die(const char *m) { fprintf(stderr, "majsim: %s\n", m); exit(2); }
static void rd(void *p, size_t sz, size_t n, FILE *f) {
  if (n && fread(p, sz, n, f) != n) die("short read");
}
static void *xmalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (!p) die("out of memory");
  return p;
}

static int64_t nV, nA;
static uint8_t *st;
static int32_t *au, *av;
static uint8_t *aw;

static int32_t newv(uint8_t s) { st[nV] = s; return (int32_t)nV++; }
static void link2(int32_t p, int32_t c, uint8_t k) {
  au[nA] = p; av[nA] = c; aw[nA] = k; nA++;
  au[nA] = c; av[nA] = p; aw[nA] = 1; nA++;
}

static void expand_timer(int32_t r, int32_t tau, int rising, int compress) {
  int64_t L = tau - 1;
  uint8_t arm = rising ? 0 : 1, cb = rising ? 1 : 0;
  int arms = compress ? 1 : 2;
  for (int k = 0; k < arms; k++) {
    int32_t prev = r;
    uint8_t w = compress ? 2 : 1; /* weight of the first link (the arms) */
    for (int64_t i = 1; i <= L; i++) {
      int32_t v = newv(arm);
      link2(prev, v, w); w = 1;
      int32_t c = newv(cb);
      link2(v, c, 1);
      if (compress) link2(c, newv(cb), 2);
      else { link2(c, newv(cb), 1); link2(c, newv(cb), 1); }
      prev = v;
    }
    int32_t a = newv(cb);
    link2(prev, a, w);
    if (compress) link2(a, newv(cb), 2);
    else { link2(a, newv(cb), 1); link2(a, newv(cb), 1); }
  }
}

static int32_t *uf;
static int32_t find(int32_t x) {
  while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; }
  return x;
}

int main(int argc, char **argv) {
  if (argc < 3) die("usage: majsim in.bin out.bin");
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  FILE *f = fopen(argv[1], "rb");
  if (!f) die("cannot open input");
  char magic[4];
  rd(magic, 1, 4, f);
  if (memcmp(magic, "MAJ2", 4)) die("bad magic");
  int32_t compress;
  rd(&compress, 4, 1, f);
  int64_t h[8];
  rd(h, 8, 8, f);
  int64_t n0 = h[0], a0 = h[1], ntim = h[2], nforced = h[3], nprobes = h[4],
          nsets = h[5], nover = h[6], Tmax = h[7];

  uint8_t *st0 = xmalloc(n0);
  rd(st0, 1, n0, f);
  int32_t *tim = xmalloc(12 * ntim);
  rd(tim, 4, 3 * ntim, f);
  int64_t n = n0, A = a0;
  for (int64_t i = 0; i < ntim; i++) {
    int64_t L = tim[3 * i + 1] - 1;
    if (L < 0) die("timer with tau < 1");
    int64_t add = compress ? 3 * L + 2 : 8 * L + 6;
    n += add; A += 2 * add;
  }
  if (n >= INT32_MAX || A >= (int64_t)UINT32_MAX) die("instance too large");
  st = xmalloc(n); au = xmalloc(4 * A); av = xmalloc(4 * A); aw = xmalloc(A);
  memcpy(st, st0, n0); free(st0);
  rd(au, 4, a0, f); rd(av, 4, a0, f); rd(aw, 1, a0, f);
  nV = n0; nA = a0;
  for (int64_t i = 0; i < ntim; i++)
    expand_timer(tim[3 * i], tim[3 * i + 1], tim[3 * i + 2], compress);
  free(tim);
  if (nV != n || nA != A) die("expansion count mismatch");

  int32_t *fv = xmalloc(4 * nforced);
  rd(fv, 4, nforced, f);
  uint8_t *fb = xmalloc(nforced * (Tmax + 1));
  rd(fb, 1, nforced * (Tmax + 1), f);
  int32_t *pv = xmalloc(4 * nprobes);
  rd(pv, 4, nprobes, f);
  int32_t *ov = xmalloc(4 * nover);
  rd(ov, 4, nover, f);
  uint8_t *ob = xmalloc(nsets * nover);
  rd(ob, 1, nsets * nover, f);
  fclose(f);

  /* structure: links are arc pairs (2k, 2k+1) */
  for (int64_t k = 0; k < A; k++)
    if (au[k] < 0 || au[k] >= n || av[k] < 0 || av[k] >= n) die("arc out of range");
  uf = xmalloc(4 * n);
  for (int64_t i = 0; i < n; i++) uf[i] = (int32_t)i;
  int64_t cycles = 0, links = A / 2, badpair = 0;
  for (int64_t k = 0; k < A; k += 2) {
    if (au[k] != av[k + 1] || av[k] != au[k + 1] || aw[k + 1] != 1) badpair++;
    int32_t x = find(au[k]), y = find(av[k]);
    if (x == y) cycles++; else uf[x] = y;
  }
  int64_t comps = 0;
  for (int64_t i = 0; i < n; i++) if (find((int32_t)i) == (int32_t)i) comps++;
  free(uf);

  uint32_t *off = xmalloc(4 * (n + 1));
  memset(off, 0, 4 * (n + 1));
  for (int64_t k = 0; k < A; k++) off[au[k] + 1]++;
  for (int64_t i = 0; i < n; i++) off[i + 1] += off[i];
  int32_t *nb = xmalloc(4 * A);
  uint8_t *wt = xmalloc(A);
  uint32_t *pos = xmalloc(4 * n);
  memcpy(pos, off, 4 * n);
  for (int64_t k = 0; k < A; k++) { uint32_t p = pos[au[k]]++; nb[p] = av[k]; wt[p] = aw[k]; }
  free(pos); free(au); free(av); free(aw);

  uint8_t *isf = xmalloc(n);
  memset(isf, 0, n);
  for (int64_t i = 0; i < nforced; i++) isf[fv[i]] = 1;
  uint16_t *deg = xmalloc(2 * n);
  int64_t maxdeg = 0, even = 0, dh[64] = {0};
  for (int64_t v = 0; v < n; v++) {
    uint32_t d = 0;
    for (uint32_t k = off[v]; k < off[v + 1]; k++) d += wt[k];
    if (d > 60000) die("degree overflow");
    deg[v] = (uint16_t)d;
    if (isf[v]) continue;
    if ((int64_t)d > maxdeg) maxdeg = d;
    if (d % 2 == 0) even++;
    dh[d < 63 ? d : 63]++;
  }

  uint8_t *x = xmalloc(n), *y = xmalloc(n);
  const char *tre = getenv("MAJSIM_TRANSIENT");
  int want_tr = tre && tre[0] == '1';
  uint8_t *w = want_tr ? xmalloc(n) : NULL;
  int64_t *stab = xmalloc(8 * (nsets ? nsets : 1));
  uint8_t *hist = xmalloc(nprobes * (Tmax + 1));
  FILE *g = fopen(argv[2], "wb");
  if (!g) die("cannot open output");
  for (int64_t s = 0; s < nsets; s++) {
    stab[s] = -1;
    memcpy(x, st, n);
    for (int64_t i = 0; i < nover; i++) x[ov[i]] = ob[s * nover + i];
    for (int64_t i = 0; i < nforced; i++) x[fv[i]] = fb[i * (Tmax + 1)];
    for (int64_t t = 0;; t++) {
      for (int64_t p = 0; p < nprobes; p++) hist[p * (Tmax + 1) + t] = x[pv[p]];
      if (t == Tmax) break;
      int diff = 0, cmp = want_tr && t >= 1;
#pragma omp parallel for schedule(static, 65536) reduction(| : diff)
      for (int64_t v = 0; v < n; v++) {
        uint32_t c = 0;
        for (uint32_t k = off[v]; k < off[v + 1]; k++) c += wt[k] * x[nb[k]];
        uint32_t c2 = 2 * c, d = deg[v];
        y[v] = c2 > d ? 1 : (c2 < d ? 0 : x[v]);
        if (cmp && y[v] != w[v]) diff = 1;
      }
      for (int64_t i = 0; i < nforced; i++) y[fv[i]] = fb[i * (Tmax + 1) + t + 1];
      if (cmp && !diff && stab[s] < 0) stab[s] = t - 1; /* x(t+1) = x(t-1) */
      if (want_tr) { uint8_t *tmp = w; w = x; x = y; y = tmp; }
      else { uint8_t *tmp = x; x = y; y = tmp; }
    }
    if (fwrite(hist, 1, nprobes * (Tmax + 1), g) != (size_t)(nprobes * (Tmax + 1))) die("write");
  }
  fclose(g);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double sec = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
  printf("{\"n\": %lld, \"links\": %lld, \"cycles\": %lld, \"components\": %lld, "
         "\"bad_pairs\": %lld, \"maxdeg\": %lld, \"even_degree\": %lld, \"deg_hist\": {",
         (long long)n, (long long)links, (long long)cycles, (long long)comps,
         (long long)badpair, (long long)maxdeg, (long long)even);
  int first = 1;
  for (int d = 0; d < 64; d++)
    if (dh[d]) { printf("%s\"%d\": %lld", first ? "" : ", ", d, (long long)dh[d]); first = 0; }
  printf("}, \"stabilization\": [");
  for (int64_t s = 0; s < nsets; s++)
    printf("%s%lld", s ? ", " : "", want_tr ? (long long)stab[s] : -2LL);
  printf("], \"seconds\": %.3f}\n", sec);
  return 0;
}
