/* Majority on trees — model of the degree-5 construction.
 *
 * Pure functions without DOM access: window.MajorityTree in the browser,
 * module.exports in Node (tests). It follows the notes of
 * research/majority-degree-20261006 (hardness-degree.txt, degree-review.txt)
 * as re-implemented and checked by research/degree5-check-20261007/deg5.py;
 * tools/test_model.cjs compares both implementations.
 *
 * Dynamics: every vertex takes the majority of its neighbours, keeping its
 * state on a tie (all degrees here are odd, so ties never happen).
 */
(function (scope) {
  "use strict";

  function fail(message) { throw new Error(message); }

  // ------------------------------------------------------------ histories
  function bitLength(x) { var n = 0; while (x > 0) { n++; x = Math.floor(x / 2); } return n; }
  /** S = ceil(log2(H + 2)) + 8, common to all generators of horizon H. */
  function S_of(H) { return bitLength(H + 1) + 8; }

  /** Binary history on t >= 0: initial bit and sorted change times (>= 1). */
  function Hist(b0, ch) { this.b0 = b0 ? 1 : 0; this.ch = ch || []; }
  Hist.prototype.K = function () { return this.ch.length; };
  Hist.prototype.q = function (t) {
    var lo = 0, hi = this.ch.length;
    while (lo < hi) { var mid = (lo + hi) >> 1; if (this.ch[mid] <= t) lo = mid + 1; else hi = mid; }
    return lo;
  };
  Hist.prototype.at = function (t) { return this.b0 ^ (this.q(t) & 1); };
  /** (G3): h_j(t) = h(t+1) xor [j = q(t+1) mod 4]. */
  Hist.prototype.child = function (j) {
    var b0 = this.at(1) ^ ((this.q(1) % 4) === j ? 1 : 0), ch = [];
    for (var a = 1; a <= this.ch.length; a++) {
      var c = this.ch[a - 1];
      if (c >= 2 && j !== (a - 1) % 4 && j !== a % 4) ch.push(c - 1);
    }
    return new Hist(b0, ch);
  };
  /** The index of the dissident child at time t: q(t+1) mod 4. */
  Hist.prototype.dissident = function (t) { return this.q(t + 1) % 4; };

  /** Root target of a word w(0..H): w(0) before S, then w(min(t - S, H)). */
  function wordHist(w) {
    var H = w.length - 1, S = S_of(H), ch = [];
    for (var t = 1; t <= H; t++) if (w[t] !== w[t - 1]) ch.push(S + t);
    return new Hist(w[0], ch);
  }
  function wordValue(w, t) {
    var H = w.length - 1, S = S_of(H);
    return t < S ? w[0] : w[Math.min(t - S, H)];
  }

  // ------------------------------------------------------------ trees
  /** A tree under construction. With compress = true, k identical private
   * copies hanging from one vertex are stored once with multiplicity k; this
   * is exact (the copies start equal and see the same parent). */
  function Graph(compress) {
    this.compress = !!compress;
    this.st = []; this.role = [];
    this.au = []; this.av = []; this.aw = [];
    this.forced = [];
  }
  Graph.prototype.add = function (s, role) {
    this.st.push(s ? 1 : 0); this.role.push(role || "");
    return this.st.length - 1;
  };
  Graph.prototype.link = function (p, c, k) {
    this.au.push(p, c); this.av.push(c, p); this.aw.push(k || 1, 1);
  };
  /** k private copies of build() hanging from parent. */
  Graph.prototype.hang = function (parent, k, build) {
    if (this.compress) {
      var one = build();
      this.link(parent, one.port, k);
      return { parts: [one], size: k * one.size, init: one.init };
    }
    var parts = [], size = 0;
    for (var i = 0; i < k; i++) {
      var p = build();
      this.link(parent, p.port, 1);
      parts.push(p); size += p.size;
    }
    return { parts: parts, size: size, init: parts[0].init };
  };
  /** A forced vertex: its state at time t is seq(t) (array or function). */
  Graph.prototype.force = function (v, seq) { this.forced.push({ v: v, seq: seq }); };

  function leaves(g, root, b, role) {
    if (g.compress) g.link(root, g.add(b, role || "leaf"), 2);
    else { g.link(root, g.add(b, role || "leaf"), 1); g.link(root, g.add(b, role || "leaf"), 1); }
  }

  /** Cherry: root and two leaves, all b. Constant b against any parent. */
  function cherry(g, b) {
    var a = g.add(b, "const");
    leaves(g, a, b, "const-leaf");
    return { kind: "const", value: b ? 1 : 0, port: a, init: b ? 1 : 0, size: 3 };
  }

  /** Two-arm timer of hardness.txt section 3: 0 before tau and 1 from tau
   * (rising), or the complement. 8 tau - 1 vertices, degree <= 3. */
  function timer(g, tau, rising) {
    if (!(tau >= 1)) fail("A timer needs a date >= 1 (got " + tau + ").");
    var L = tau - 1, arm = rising ? 0 : 1, cb = rising ? 1 : 0;
    var r = g.add(arm, "timer");
    var arms = [];
    for (var k = 0; k < (g.compress ? 1 : 2); k++) {
      var prev = r, w = g.compress ? 2 : 1, nodes = [];
      for (var i = 1; i <= L; i++) {
        var v = g.add(arm, "arm");
        g.link(prev, v, w); w = 1;
        var c = g.add(cb, "const");
        g.link(v, c, 1);
        leaves(g, c, cb, "const-leaf");
        nodes.push({ v: v, c: c });
        prev = v;
      }
      var a = g.add(cb, "const");
      g.link(prev, a, w);
      leaves(g, a, cb, "const-leaf");
      arms.push({ nodes: nodes, end: a });
    }
    return { kind: "timer", tau: tau, rising: !!rising, port: r, init: arm, size: 8 * tau - 1, arms: arms };
  }

  /** Pulse P[a,b) = [a <= t < b] (or its complement), degree-review.txt
   * section 1: a chain of a roots; level l has children D_(b-l-1), 0,
   * U_(a-l-1) and the next root; the last one D_(b-a), 0, 1, D_(b-a). */
  function pulse(g, a, b, neg) {
    if (!(a >= 1 && a < b)) fail("A pulse needs 1 <= a < b (got " + a + ", " + b + ").");
    var top = null, prev = null, size = 0, levels = [];
    for (var l = 0; l < a; l++) {
      var aa = a - l, bb = b - l;
      var r = g.add(neg ? 1 : 0, "pulse");
      if (prev === null) top = r; else g.link(prev, r, 1);
      var lev = { root: r, a: aa, b: bb };
      var D = g.hang(r, aa === 1 ? 2 : 1, function () { return timer(g, bb - 1, !!neg); });
      var Z = g.hang(r, 1, function () { return cherry(g, neg ? 1 : 0); });
      var X = aa === 1 ? g.hang(r, 1, function () { return cherry(g, neg ? 0 : 1); })
                       : g.hang(r, 1, function () { return timer(g, aa - 1, !neg); });
      lev.D = D.parts; lev.zero = Z.parts[0]; lev.third = X.parts[0];
      size += 1 + D.size + Z.size + X.size;
      levels.push(lev);
      prev = r;
    }
    return { kind: "pulse", a: a, b: b, neg: !!neg, port: top, init: neg ? 1 : 0, size: size, levels: levels };
  }

  /** The degree-5 word generator: four-child recursion while K > 2, then a
   * cherry (K = 0), a timer (K = 1) or a pulse (K = 2). */
  function generator(g, h, depth) {
    depth = depth || 0;
    var K = h.K();
    if (K === 0) return Object.assign(cherry(g, h.b0), { hist: h, depth: depth });
    if (K === 1) return Object.assign(timer(g, h.ch[0], h.b0 === 0), { hist: h, depth: depth });
    if (K === 2) return Object.assign(pulse(g, h.ch[0], h.ch[1], h.b0 === 1), { hist: h, depth: depth });
    var r = g.add(h.b0, "node"), children = [], size = 1;
    for (var j = 0; j < 4; j++) {
      var c = h.child(j);
      var part = g.hang(r, 1, function () { return generator(g, c, depth + 1); });
      children.push(part.parts[0]); size += part.size;
    }
    return { kind: "node", port: r, init: h.b0, size: size, hist: h, depth: depth, children: children };
  }

  // Sizes of the plain (uncompressed) tree, without building it.
  function timerSize(tau) { return 8 * tau - 1; }
  function pulseSize(a, b) {
    var s = 0;
    for (var l = 0; l < a; l++) {
      var aa = a - l, bb = b - l;
      s += 1 + (aa === 1 ? 2 * timerSize(bb - 1) + 3 + 3 : timerSize(bb - 1) + 3 + timerSize(aa - 1));
    }
    return s;
  }
  function generatorSize(h) {
    var K = h.K();
    if (K === 0) return 3;
    if (K === 1) return timerSize(h.ch[0]);
    if (K === 2) return pulseSize(h.ch[0], h.ch[1]);
    var s = 1;
    for (var j = 0; j < 4; j++) s += generatorSize(h.child(j));
    return s;
  }
  function generatorShape(h) {
    var K = h.K();
    if (K <= 2) return { depth: 0, leaves: 1, nodes: 0, pulses: K === 2 ? 1 : 0 };
    var out = { depth: 0, leaves: 0, nodes: 1, pulses: 0 };
    for (var j = 0; j < 4; j++) {
      var c = generatorShape(h.child(j));
      out.depth = Math.max(out.depth, c.depth + 1);
      out.leaves += c.leaves; out.nodes += c.nodes; out.pulses += c.pulses;
    }
    return out;
  }

  // ------------------------------------------------------------ simulation
  function compile(g) {
    var n = g.st.length, A = g.au.length, k, i;
    var off = new Int32Array(n + 1);
    for (k = 0; k < A; k++) off[g.au[k] + 1]++;
    for (i = 0; i < n; i++) off[i + 1] += off[i];
    var nb = new Int32Array(A), wt = new Uint8Array(A), pos = off.slice(0, n);
    for (k = 0; k < A; k++) { var p = pos[g.au[k]]++; nb[p] = g.av[k]; wt[p] = g.aw[k]; }
    var deg = new Uint16Array(n);
    for (i = 0; i < n; i++) { var d = 0; for (k = off[i]; k < off[i + 1]; k++) d += wt[k]; deg[i] = d; }
    return { n: n, off: off, nb: nb, wt: wt, deg: deg };
  }
  function seqAt(seq, t) { return typeof seq === "function" ? (seq(t) ? 1 : 0) : (seq[Math.min(t, seq.length - 1)] ? 1 : 0); }

  /** Synchronous majority with ties kept. opts.init: [[v, bit]];
   * opts.frames: keep every configuration (small trees); otherwise the
   * result has, for every vertex, its list of change times. opts.events:
   * sorted times at which some forced input may change; between them, a
   * fixed point is skipped in one jump (used for long, quiet horizons). */
  function simulate(g, Tmax, opts) {
    opts = opts || {};
    var c = g._csr || (g._csr = compile(g));
    var n = c.n, off = c.off, nb = c.nb, wt = c.wt, deg = c.deg;
    var x = Uint8Array.from(g.st), y = new Uint8Array(n);
    (opts.init || []).forEach(function (p) { x[p[0]] = p[1] ? 1 : 0; });
    var forced = g.forced;
    forced.forEach(function (f) { x[f.v] = seqAt(f.seq, 0); });
    var frames = opts.frames ? [x.slice()] : null;
    var start = x.slice(), changes = opts.frames ? null : new Array(n);
    var events = opts.events || null, ei = 0;
    var t = 0;
    while (t < Tmax) {
      var moved = false;
      for (var v = 0; v < n; v++) {
        var s = 0;
        for (var k = off[v]; k < off[v + 1]; k++) s += wt[k] * x[nb[k]];
        var s2 = 2 * s, d = deg[v];
        var nv = s2 > d ? 1 : (s2 < d ? 0 : x[v]);
        y[v] = nv;
      }
      for (var f = 0; f < forced.length; f++) y[forced[f].v] = seqAt(forced[f].seq, t + 1);
      for (v = 0; v < n; v++) {
        if (y[v] !== x[v]) {
          moved = true;
          if (changes) (changes[v] || (changes[v] = [])).push(t + 1);
        }
      }
      var tmp = x; x = y; y = tmp;
      t++;
      if (frames) frames.push(x.slice());
      if (!moved && events && !frames) {
        while (ei < events.length && events[ei] <= t) ei++;
        var next = ei < events.length ? events[ei] - 1 : Tmax;
        if (next > t) t = Math.min(next, Tmax);
      }
    }
    return { n: n, Tmax: Tmax, frames: frames, start: start, changes: changes, final: x };
  }
  /** State of vertex v at time t from a change-list result. */
  function stateAt(res, v, t) {
    if (res.frames) return res.frames[Math.min(t, res.frames.length - 1)][v];
    var ch = res.changes[v], s = res.start[v];
    if (!ch) return s;
    var lo = 0, hi = ch.length;
    while (lo < hi) { var mid = (lo + hi) >> 1; if (ch[mid] <= t) lo = mid + 1; else hi = mid; }
    return s ^ (lo & 1);
  }

  /** Consumer histories used to test robustness. */
  function consumer(kind, expected, seed) {
    var rnd = mulberry32(seed || 1);
    var n = expected.length, out = new Array(n);
    for (var t = 0; t < n; t++) {
      out[t] = kind === "zeros" ? 0 : kind === "ones" ? 1 :
        kind === "anti" ? (t + 1 < n ? 1 - expected[t + 1] : 0) :
        kind === "lag" ? 1 - expected[t] : (rnd() < 0.5 ? 1 : 0);
    }
    return out;
  }
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // ------------------------------------------------------------ circuits
  // validate / evaluate / lower / toGates are adapted from
  // gadgets-site/assets/grid-model.js (the two-dimensional compiler).
  var OPS = ["AND", "OR", "NOT", "NAND", "NOR", "XOR", "XNOR"];
  var ZERO = "@0", ONE = "@1";

  function validate(raw) {
    if (!raw || !Array.isArray(raw.inputs) || !Array.isArray(raw.gates)) fail("The circuit needs inputs and gates.");
    var names = new Set(), valid = /^[A-Za-z][A-Za-z0-9_]{0,19}$/;
    var inputs = raw.inputs.map(function (v) {
      return typeof v === "string" ? { id: v, value: 0 } : { id: String(v.id || ""), value: v.value === undefined ? 0 : Number(v.value) };
    });
    inputs.forEach(function (v) {
      if (!valid.test(v.id) || names.has(v.id)) fail("Invalid or repeated name: " + v.id + ".");
      if (v.value !== 0 && v.value !== 1) fail("Input " + v.id + " must be 0 or 1.");
      names.add(v.id);
    });
    var gates = raw.gates.map(function (g) {
      return { id: String(g.id || ""), op: String(g.op || "").toUpperCase(), a: String(g.a || ""), b: String(g.b || "") };
    });
    gates.forEach(function (g) {
      if (!valid.test(g.id) || names.has(g.id)) fail("Invalid or repeated name: " + g.id + ".");
      if (OPS.indexOf(g.op) < 0) fail("Unknown gate " + g.op + " in " + g.id + ".");
      names.add(g.id);
    });
    var known = function (x) { return names.has(x) || x === "0" || x === "1"; };
    gates.forEach(function (g) {
      (g.op === "NOT" ? [g.a] : [g.a, g.b]).forEach(function (x) {
        if (!known(x)) fail(g.id + ": the connection “" + (x || "empty") + "” does not exist.");
      });
    });
    var output = String(raw.output || "");
    if (!known(output)) fail("Choose an output node that exists.");
    var byId = new Map(gates.map(function (g) { return [g.id, g]; })), mark = new Map(), ordered = [];
    function visit(id) {
      if (!byId.has(id)) return;
      if (mark.get(id) === 1) fail("The circuit has a cycle through " + id + ".");
      if (mark.get(id) === 2) return;
      mark.set(id, 1);
      var g = byId.get(id);
      visit(g.a);
      if (g.op !== "NOT") visit(g.b);
      mark.set(id, 2);
      ordered.push(g);
    }
    gates.forEach(function (g) { visit(g.id); });
    return { version: 1, inputs: inputs, gates: ordered, output: output };
  }

  function evaluate(def, assignment) {
    assignment = assignment || {};
    var values = Object.assign(Object.create(null), { "0": 0, "1": 1 });
    def.inputs.forEach(function (i) {
      var v = Object.prototype.hasOwnProperty.call(assignment, i.id) ? assignment[i.id] : i.value;
      values[i.id] = v;
    });
    def.gates.forEach(function (g) {
      var a = values[g.a], b = values[g.b];
      values[g.id] = g.op === "NOT" ? 1 - a : g.op === "AND" ? (a & b) : g.op === "OR" ? (a | b) :
        g.op === "NAND" ? 1 - (a & b) : g.op === "NOR" ? 1 - (a | b) : g.op === "XOR" ? (a ^ b) : 1 - (a ^ b);
    });
    return values;
  }

  /** Negations pushed to the inputs; only AND and OR remain. */
  function lower(def) {
    var byId = new Map(def.gates.map(function (g) { return [g.id, g]; }));
    var memo = new Map(), intern = new Map(), sources = [], gates = [], labels = new Map();
    function binary(op, a, b, owner, negative) {
      if (a === b) return a;
      if (op === "and") { if (a === ZERO || b === ZERO) return ZERO; if (a === ONE) return b; if (b === ONE) return a; }
      if (op === "or") { if (a === ONE || b === ONE) return ONE; if (a === ZERO) return b; if (b === ZERO) return a; }
      var key = op + ":" + [a, b].sort().join(",");
      if (intern.has(key)) return intern.get(key);
      var id = "g" + gates.length;
      gates.push({ id: id, op: op, a: a, b: b, owner: owner, negative: negative });
      intern.set(key, id);
      labels.set(id, (negative ? "¬" : "") + owner);
      return id;
    }
    function get(id, neg) {
      neg = !!neg;
      var key = id + ":" + Number(neg);
      if (memo.has(key)) return memo.get(key);
      var result;
      if (id === "0" || id === "1") result = Number(id) ^ Number(neg) ? ONE : ZERO;
      else if (!byId.has(id)) {
        result = "i:" + id + ":" + Number(neg);
        sources.push({ id: result, input: id, negative: neg });
        labels.set(result, (neg ? "¬" : "") + id);
      } else {
        var g = byId.get(id), p = neg, op = g.op;
        if (op === "NOT") result = get(g.a, !p);
        else {
          if (op === "NAND") { p = !p; op = "AND"; }
          if (op === "NOR") { p = !p; op = "OR"; }
          if (op === "XNOR") { p = !p; op = "XOR"; }
          if (op === "AND" || op === "OR") result = binary((op === "AND") !== p ? "and" : "or", get(g.a, p), get(g.b, p), id, neg);
          else {
            var ap = get(g.a, false), an = get(g.a, true), bp = get(g.b, false), bn = get(g.b, true);
            result = binary("or", binary("and", ap, p ? bp : bn, id, neg), binary("and", an, p ? bn : bp, id, neg), id, neg);
          }
        }
      }
      memo.set(key, result);
      return result;
    }
    var output = get(def.output);
    var needed = new Set(), map = new Map(gates.map(function (g) { return [g.id, g]; }));
    (function need(id) {
      if (needed.has(id)) return;
      needed.add(id);
      var g = map.get(id);
      if (g) { need(g.a); need(g.b); }
    })(output);
    return {
      sources: sources.filter(function (s) { return needed.has(s.id); }),
      gates: gates.filter(function (g) { return needed.has(g.id); }),
      output: output, labels: labels
    };
  }

  /** MCVP: input constants first, then gates; nodes[i-1] =
   * {kind: "const", input, negative} or {kind: "and"|"or", p, q}, p, q < i.
   * Input values are not part of the structure (see inputBits). */
  function toMcvp(def) {
    var low = lower(def), index = new Map(), nodes = [], names = [];
    if (low.output === ZERO || low.output === ONE) {
      return { nodes: [{ kind: "const", fixed: low.output === ONE ? 1 : 0 }], names: [low.output === ONE ? "1" : "0"] };
    }
    low.sources.forEach(function (s) {
      nodes.push({ kind: "const", input: s.input, negative: s.negative });
      names.push(low.labels.get(s.id));
      index.set(s.id, nodes.length);
    });
    if (index.has(low.output)) {
      var only = nodes[index.get(low.output) - 1];
      return { nodes: [only], names: [low.labels.get(low.output)] };
    }
    low.gates.forEach(function (g) {
      var a = index.get(g.a), b = index.get(g.b);
      nodes.push({ kind: g.op, p: Math.min(a, b), q: Math.max(a, b) });
      names.push(low.labels.get(g.id));
      index.set(g.id, nodes.length);
    });
    if (index.get(low.output) !== nodes.length) fail("Internal error: the output is not the last node.");
    return { nodes: nodes, names: names };
  }
  /** Bits of the input nodes for an assignment of the original inputs. */
  function inputBits(mcvp, def, assignment) {
    var vals = {};
    def.inputs.forEach(function (i) {
      vals[i.id] = Object.prototype.hasOwnProperty.call(assignment || {}, i.id) ? assignment[i.id] : i.value;
    });
    return mcvp.nodes.map(function (nd) {
      if (nd.kind !== "const") return null;
      if (nd.fixed !== undefined) return nd.fixed;
      return (vals[nd.input] ? 1 : 0) ^ (nd.negative ? 1 : 0);
    });
  }
  function mcvpValues(mcvp, bits) {
    var val = [];
    mcvp.nodes.forEach(function (nd, i) {
      if (nd.kind === "const") val.push(bits[i]);
      else { var a = val[nd.p - 1], b = val[nd.q - 1]; val.push(nd.kind === "and" ? (a & b) : (a | b)); }
    });
    return val;
  }

  // ------------------------------------------------------------ program
  var HOLD = [1, 1, 1], RESET = [0, 0, 0], LOAD = [2, 2, 2];

  function cellNames(M) {
    var names = ["g"], edges = [["g", "b1"]], i;
    for (i = 1; i <= M; i++) names.push("b" + i);
    for (i = 1; i <= M; i++) names.push("c" + i);
    for (i = 1; i <= M; i++) names.push("r" + i);
    names.push("cA", "rA", "cB", "rB");
    for (i = 1; i < M; i++) edges.push(["b" + i, "b" + (i + 1)]);
    for (i = 1; i <= M; i++) edges.push(["b" + i, "c" + i]);
    for (i = 1; i <= M; i++) edges.push(["c" + i, "r" + i]);
    edges.push(["g", "cA"], ["cA", "rA"], ["g", "cB"], ["cB", "rB"]);
    return { names: names, edges: edges };
  }

  /** hardness-degree.txt section 3: logical edge "u|v" -> main node of u. */
  function portAssignment(M) {
    var P = { "g|cA": "A", "g|cB": "B", "g|b1": "C" };
    for (var i = 1; i <= M; i++) {
      var b = "b" + i, c = "c" + i, r = "r" + i, pred = i === 1 ? "g" : "b" + (i - 1);
      P[b + "|" + pred] = "A";
      if (i < M) { P[b + "|b" + (i + 1)] = "B"; P[b + "|" + c] = "C"; }
      else P[b + "|" + c] = "B";
      P[c + "|" + b] = "A"; P[c + "|" + r] = "B"; P[r + "|" + c] = "A";
    }
    ["A", "B"].forEach(function (X) {
      P["c" + X + "|g"] = "A"; P["c" + X + "|r" + X] = "B"; P["r" + X + "|c" + X] = "A";
    });
    return P;
  }

  /** The serial program of hardness-degree.txt sections 4-6. Each step maps
   * cells to control counts (u_A, u_C, u_B); "ins" is the instruction tree. */
  function Program(cellIndex) {
    this.ci = cellIndex; this.steps = []; this.root = { name: "program", start: 0, children: [] };
    this.stack = [this.root];
  }
  Program.prototype.begin = function (name, info) {
    var node = { name: name, start: this.steps.length, children: [], info: info || null };
    this.stack[this.stack.length - 1].children.push(node);
    this.stack.push(node);
  };
  Program.prototype.end = function () { var n = this.stack.pop(); n.len = this.steps.length - n.start; return n; };
  Program.prototype.put = function (n, modes) {
    var entry = Object.keys(modes).map(function (name) { return [this.ci[name]].concat(modes[name]); }, this);
    for (var i = 0; i < n; i++) this.steps.push(entry);
  };
  Program.prototype.clear = function (v) { this.begin("CLEAR(" + v + ")"); var m = {}; m[v] = RESET; this.put(4, m); this.end(); };
  Program.prototype.copy = function (a, b, extra) {
    this.begin("COPY(" + a + "→" + b + ")");
    var m = Object.assign({}, extra || {}); m[b] = RESET; this.put(4, m);
    m = Object.assign({}, extra || {}); m[b] = LOAD; this.put(4, m);
    this.end();
  };
  Program.prototype.move = function (a, b) { this.begin("MOVE(" + a + "→" + b + ")"); this.copy(a, b); this.clear(a); this.end(); };
  Program.prototype.store = function (X) {
    this.begin("STORE(g→r" + X + ")");
    this.copy("g", "c" + X); this.copy("c" + X, "r" + X); this.clear("c" + X); this.clear("g");
    this.end();
  };
  Program.prototype.read = function (i, X) {
    this.begin("READ(" + i + "," + X + ")", { kind: "read", node: i, temp: X });
    this.copy("r" + i, "c" + i); this.copy("c" + i, "b" + i); this.clear("c" + i);
    for (var k = i; k > 1; k--) this.move("b" + k, "b" + (k - 1));
    this.move("b1", "g");
    this.store(X);
    this.end();
  };
  Program.prototype.gate = function (op) {
    var uc = op === "and" ? 1 : 2, g0 = { g: RESET };
    this.begin("GATE(" + op.toUpperCase() + ")", { kind: "gate", op: op });
    this.begin("phase 0: load the connectors, g held at 0"); this.copy("rA", "cA", g0); this.copy("rB", "cB", g0); this.end();
    this.begin("phase 1: ends of g take A and B"); this.put(2, { g: [2, 0, 2] }); this.end();
    this.begin("phase 2: centre of g computes " + op.toUpperCase()); this.put(1, { g: [1, uc, 1] }); this.end();
    this.begin("phase 3: clear both connectors"); this.put(4, { g: [1, uc, 1], cA: RESET, cB: RESET }); this.end();
    this.begin("phase 4: settle the ends"); this.put(2, { g: [1, uc, 1] }); this.end();
    this.begin("phase 5: ends copy the centre"); this.put(2, { g: [2, uc, 2] }); this.end();
    this.end();
  };
  Program.prototype.write = function (i) {
    this.begin("WRITE(" + i + ")", { kind: "write", node: i });
    this.move("g", "b1");
    for (var k = 1; k < i; k++) this.move("b" + k, "b" + (k + 1));
    this.copy("b" + i, "c" + i); this.copy("c" + i, "r" + i); this.clear("c" + i); this.clear("b" + i);
    this.end();
  };

  /** Compile an MCVP structure into the degree-5 plan. opts.H overrides
   * H = 200 M^2 + 200; opts.ever adds the receiver z. */
  function plan(mcvp, opts) {
    opts = opts || {};
    var nodes = mcvp.nodes, M = nodes.length;
    var cn = cellNames(M), ci = {};
    cn.names.forEach(function (n, i) { ci[n] = i; });
    var P = new Program(ci), checkpoints = [];
    nodes.forEach(function (nd, idx) {
      var i = idx + 1;
      if (nd.kind === "const") return;
      P.begin("gate " + i + " = " + nd.kind.toUpperCase() + "(" + nd.p + ", " + nd.q + ")", { kind: "node", node: i });
      P.read(nd.p, "A"); P.read(nd.q, "B"); P.gate(nd.kind); P.write(i);
      P.begin("CLEAR temporaries"); P.clear("rA"); P.clear("rB"); P.end();
      P.end();
      checkpoints.push([P.steps.length, i]);
    });
    var L = P.steps.length;
    var H = opts.H || 200 * M * M + 200;
    if (L + 1 > H) fail("H is too small for the program (" + L + " steps).");
    var S = S_of(H), T = S + H;
    // Per cell, the sparse list of (step index >= 1, u triple).
    var modes = cn.names.map(function () { return []; });
    P.steps.forEach(function (entry, s) {
      entry.forEach(function (e) { modes[e[0]].push([s + 1, e[1], e[2], e[3]]); });
    });
    var port = portAssignment(M);
    var links = cn.edges.map(function (e) {
      return { u: e[0], v: e[1], pu: port[e[0] + "|" + e[1]], pv: port[e[1] + "|" + e[0]] };
    });
    var used = {};
    links.forEach(function (l) { used[l.u + "." + l.pu] = 1; used[l.v + "." + l.pv] = 1; });
    var out = "r" + M;
    if (opts.ever) used[out + ".B"] = 1;
    var p = {
      M: M, nodes: nodes, names: mcvp.names || null, cells: cn.names, cellIndex: ci, links: links,
      used: used, out: out, ever: !!opts.ever, L: L, H: H, S: S, T: T, modes: modes,
      program: P.root, checkpoints: checkpoints
    };
    p.root = P.root; P.root.len = L;
    return p;
  }

  /** u of node xi (0 = A, 1 = C, 2 = B) of cell c at abstract time idx. */
  function uAt(p, c, xi, idx) {
    if (idx <= 0 || idx > p.L) return 1;
    var list = p.modes[c], lo = 0, hi = list.length;
    while (lo < hi) { var mid = (lo + hi) >> 1; if (list[mid][0] < idx) lo = mid + 1; else hi = mid; }
    return lo < list.length && list[lo][0] === idx ? list[lo][1 + xi] : 1;
  }
  function physIdx(p, t) { return t < p.S ? 0 : Math.min(t - p.S, p.H); }

  /** Root history of control j (1, 2) of node xi of cell c. */
  function controlHist(p, c, xi, j) {
    var prev = j <= 1 ? 1 : 0, ch = [], list = p.modes[c];
    var last = 0;
    for (var k = 0; k < list.length; k++) {
      var idx = list[k][0];
      if (idx > last + 1 && prev !== (j <= 1 ? 1 : 0)) { ch.push(p.S + last + 1); prev = j <= 1 ? 1 : 0; }
      var v = j <= list[k][1 + xi] ? 1 : 0;
      if (v !== prev) { ch.push(p.S + idx); prev = v; }
      last = idx;
    }
    if (prev !== (j <= 1 ? 1 : 0)) ch.push(p.S + last + 1);
    return new Hist(j <= 1 ? 1 : 0, ch);
  }
  /** The control word itself, w(0..H). */
  function controlWord(p, c, xi, j) {
    var w = new Uint8Array(p.H + 1);
    for (var t = 0; t <= p.H; t++) w[t] = j <= uAt(p, c, xi, t) ? 1 : 0;
    return w;
  }

  /** Vertex count of the full tree (cells, leaves, constants, every
   * generator) without building it. */
  function treeSize(p) {
    var total = 0, gens = 0, maxGen = 0;
    var cache = new Map();
    p.cells.forEach(function (name, c) {
      total += 5;
      for (var xi = 0; xi < 3; xi++) {
        for (var j = 1; j <= 2; j++) {
          var h = controlHist(p, c, xi, j), key = h.b0 + ":" + h.ch.join(",");
          var s = cache.get(key);
          if (s === undefined) { s = generatorSize(h); cache.set(key, s); }
          total += s; gens++; maxGen = Math.max(maxGen, s);
        }
      }
      ["A", "C", "B"].forEach(function (X) { if (!p.used[name + "." + X]) total += 3; });
    });
    if (p.ever) total += 2 + timerSize(p.T + 1);
    return { vertices: total, generators: gens, largestGenerator: maxGen };
  }

  /** The macrocell level: every macrocell, leaf and constant port exactly,
   * each control as a vertex that follows its word (the generator contract,
   * checked separately), and the receiver z with its leaf and timer. */
  function macroGraph(p, bits) {
    var g = new Graph(true), id = {};
    p.cells.forEach(function (name, c) {
      var reg = /^r(\d+)$/.exec(name), b = 0;
      if (reg && bits && bits[Number(reg[1]) - 1] !== null && bits[Number(reg[1]) - 1] !== undefined) b = bits[Number(reg[1]) - 1];
      var A = g.add(b, "A"), C = g.add(b, "C"), B = g.add(b, "B"), a = g.add(b, "leaf"), bb = g.add(b, "leaf");
      g.link(A, C); g.link(C, B); g.link(A, a); g.link(B, bb);
      id[name] = { A: A, C: C, B: B, a: a, b: bb, ctrl: [] };
      [A, C, B].forEach(function (v, xi) {
        for (var j = 1; j <= 2; j++) {
          var e = g.add(j <= 1 ? 1 : 0, "control");
          g.link(v, e);
          g.force(e, (function (cc, x, jj) {
            return function (t) { return jj <= uAt(p, cc, x, physIdx(p, t)) ? 1 : 0; };
          })(c, xi, j));
          id[name].ctrl.push(e);
        }
      });
    });
    p.links.forEach(function (l) { g.link(id[l.u][l.pu], id[l.v][l.pv]); });
    var z = null;
    if (p.ever) {
      z = g.add(0, "z");
      g.link(z, g.add(0, "leaf"));
      g.link(id[p.out].B, z);
      var tm = g.add(0, "timer");
      g.link(z, tm);
      g.force(tm, function (t) { return t >= p.T + 1 ? 1 : 0; });
    }
    p.cells.forEach(function (name) {
      ["A", "C", "B"].forEach(function (X) {
        if (!p.used[name + "." + X]) g.link(id[name][X], cherry(g, 0).port);
      });
    });
    return { graph: g, id: id, z: z };
  }

  /** Times at which some control may change (for skipping quiet stretches). */
  function controlEvents(p) {
    var ev = new Set([p.S, p.S + 1]);
    p.modes.forEach(function (list) {
      list.forEach(function (m) { ev.add(p.S + m[0]); ev.add(p.S + m[0] + 1); });
    });
    ev.add(p.T + 1); ev.add(p.T + 2);
    return Array.from(ev).sort(function (a, b) { return a - b; });
  }

  /** Simulate the macrocell level for one bit vector of the input nodes. */
  function runMacro(p, bits, Tmax) {
    var mg = macroGraph(p, bits);
    var res = simulate(mg.graph, Tmax || p.T + 6, { events: controlEvents(p) });
    return { graph: mg.graph, id: mg.id, z: mg.z, res: res };
  }

  /** Expected register contents once gates <= done are processed. */
  function expectedCells(p, bits, done) {
    var val = mcvpValues({ nodes: p.nodes }, bits), exp = {};
    p.cells.forEach(function (n) { exp[n] = 0; });
    p.nodes.forEach(function (nd, idx) {
      var i = idx + 1;
      if (nd.kind === "const" || i <= done) exp["r" + i] = val[i - 1];
    });
    return exp;
  }

  /** Check one run: every macrocell quiescent with the right bit before the
   * program, after every gate and at T; the output; z (EVER). */
  function checkRun(p, bits, run) {
    var problems = [], val = mcvpValues({ nodes: p.nodes }, bits);
    var marks = [[p.S + 1, 0]].concat(p.checkpoints.map(function (c) { return [p.S + c[0] + 1, c[1]]; }), [[p.T, p.M]]);
    marks.forEach(function (m) {
      var exp = expectedCells(p, bits, m[1]);
      p.cells.forEach(function (name) {
        var v = run.id[name], want = exp[name];
        [v.A, v.C, v.B, v.a, v.b].forEach(function (x) {
          if (stateAt(run.res, x, m[0]) !== want) problems.push("cell " + name + " at t = " + m[0] + " (after gate " + m[1] + ")");
        });
      });
    });
    var o = run.id[p.out];
    var outT = [o.A, o.C, o.B].map(function (x) { return stateAt(run.res, x, p.T); });
    if (outT.some(function (b) { return b !== val[val.length - 1]; })) problems.push("output at T");
    var z = null;
    if (run.z !== null) {
      var early = false, ever = false;
      for (var t = 0; t <= p.T + 6; t++) {
        var s = stateAt(run.res, run.z, t);
        if (s && t <= p.T + 1) early = true;
        if (s) ever = true;
      }
      if (early) problems.push("z active before T + 2");
      if (ever !== !!val[val.length - 1]) problems.push("EVER answer");
      z = { ever: ever, at: stateAt(run.res, run.z, p.T + 2) };
    }
    return { ok: problems.length === 0, problems: unique(problems).slice(0, 12), output: outT[0], expected: val[val.length - 1], z: z, values: val };
  }
  function unique(a) { var s = new Set(); return a.filter(function (x) { if (s.has(x)) return false; s.add(x); return true; }); }

  // ------------------------------------------------------------ the full tree, lazily
  // A private subtree of the full tree, described without building it. Its
  // root follows value(t): the generator contract, the pulse and timer lemmas
  // and the constants. kinds: node (recursion, history h), pulse (level of a
  // pulse chain), timer, arm (vertex v_i of a timer arm), cherry, leaf.
  function sub(kind, o) { return Object.assign({ kind: kind }, o || {}); }
  function subOfHist(h) {
    var K = h.K();
    if (K === 0) return sub("cherry", { b: h.b0 });
    if (K === 1) return sub("timer", { tau: h.ch[0], rising: h.b0 === 0 });
    if (K === 2) return sub("pulse", { a: h.ch[0], b: h.ch[1], neg: h.b0 === 1 });
    return sub("node", { h: h });
  }
  function subValue(s, t) {
    switch (s.kind) {
      case "node": return s.h.at(t);
      case "pulse": return ((s.a <= t && t < s.b) !== s.neg) ? 1 : 0;
      case "timer": return (t >= s.tau) === s.rising ? 1 : 0;
      case "arm": return (t >= s.tau - s.i) === s.rising ? 1 : 0;      // v_i turns at L + 1 - i
      default: return s.b ? 1 : 0;
    }
  }
  function subChanges(s) {
    switch (s.kind) {
      case "node": return s.h.ch.slice();
      case "pulse": return [s.a, s.b];
      case "timer": return [s.tau];
      case "arm": return s.tau - s.i >= 1 ? [s.tau - s.i] : [];
      default: return [];
    }
  }
  function subChildren(s) {
    var c, L;
    switch (s.kind) {
      case "node": return [0, 1, 2, 3].map(function (j) { return subOfHist(s.h.child(j)); });
      case "pulse":
        if (s.a === 1) return [sub("timer", { tau: s.b - 1, rising: s.neg }), sub("timer", { tau: s.b - 1, rising: s.neg }),
          sub("cherry", { b: s.neg ? 1 : 0 }), sub("cherry", { b: s.neg ? 0 : 1 })];
        return [sub("timer", { tau: s.b - 1, rising: s.neg }), sub("cherry", { b: s.neg ? 1 : 0 }),
          sub("timer", { tau: s.a - 1, rising: !s.neg }), sub("pulse", { a: s.a - 1, b: s.b - 1, neg: s.neg })];
      case "timer":
        c = s.rising ? 1 : 0; L = s.tau - 1;
        if (L === 0) return [sub("cherry", { b: c }), sub("cherry", { b: c })];
        return [sub("arm", { tau: s.tau, rising: s.rising, i: 1 }), sub("arm", { tau: s.tau, rising: s.rising, i: 1 })];
      case "arm":
        c = s.rising ? 1 : 0; L = s.tau - 1;
        return [sub("cherry", { b: c }), s.i < L ? sub("arm", { tau: s.tau, rising: s.rising, i: s.i + 1 }) : sub("cherry", { b: c })];
      case "cherry": return [sub("leaf", { b: s.b }), sub("leaf", { b: s.b })];
      default: return [];
    }
  }
  function subSize(s) {
    switch (s.kind) {
      case "node": return generatorSize(s.h);
      case "pulse": return pulseSize(s.a, s.b);
      case "timer": return timerSize(s.tau);
      case "arm": return 4 * (s.tau - s.i) + 3;          // v_i .. v_L with their cherries, and the end a
      case "cherry": return 3;
      default: return 1;
    }
  }
  function subLabel(s) {
    switch (s.kind) {
      case "node": return "node, " + s.h.K() + " changes";
      case "pulse": return (s.neg ? "¬P" : "P") + "[" + s.a + "," + s.b + ")";
      case "timer": return (s.rising ? "U" : "D") + s.tau;
      case "arm": return "arm from v" + s.i;
      case "cherry": return "constant " + s.b;
      default: return "leaf";
    }
  }

  /** Index of the macrocell tree for the explorer: which vertices stand for
   * whole subtrees (controls, the receiver's timer, the constant cherries). */
  function fullIndex(p, run) {
    var g = run.graph, n = g.st.length, adj = g.st.map(function () { return []; });
    for (var k = 0; k < g.au.length; k += 2) { adj[g.au[k]].push(g.av[k]); adj[g.av[k]].push(g.au[k]); }
    var subAt = {}, skip = {}, label = {};
    p.cells.forEach(function (name, ci) {
      var v = run.id[name];
      ["A", "C", "B"].forEach(function (X, xi) {
        label[v[X]] = name + "." + X;
        for (var j = 1; j <= 2; j++) subAt[v.ctrl[xi * 2 + j - 1]] = { s: subOfHist(controlHist(p, ci, xi, j)), what: "control " + j + " of " + name + "." + X };
      });
      label[v.a] = name + ".A'"; label[v.b] = name + ".B'";
    });
    for (var u = 0; u < n; u++) {
      if (g.role[u] === "const") subAt[u] = { s: sub("cherry", { b: g.st[u] }), what: "constant-0 cherry on an unused port" };
      if (g.role[u] === "const-leaf") skip[u] = true;
      if (g.role[u] === "timer") subAt[u] = { s: sub("timer", { tau: p.T + 1, rising: true }), what: "timer of the receiver z" };
    }
    if (run.z !== null) {
      label[run.z] = "z";
      adj[run.z].forEach(function (x) { if (g.role[x] === "leaf") label[x] = "z'"; });
    }
    var total = 0;
    for (u = 0; u < n; u++) if (!skip[u]) total += subAt[u] ? subSize(subAt[u].s) : 1;
    return { adj: adj, subAt: subAt, skip: skip, label: label, total: total, run: run, p: p };
  }

  /** The explorer's view of the full tree from macro vertex root: the root and
   * every key in open are expanded; any other subtree is one box. */
  function explore(ix, root, open, limit) {
    limit = limit || 20000;
    var count = 0, side = {};
    var isOpen = function (key) { return open.all || open.has(key); };
    // Vertices of the full tree behind each macro vertex, seen from root.
    (function sizes() {
      var order = [], parent = {}, stack = [root];
      parent[root] = -1;
      while (stack.length) {
        var v = stack.pop(); order.push(v);
        ix.adj[v].forEach(function (u) { if (u !== parent[v] && !ix.skip[u] && parent[u] === undefined) { parent[u] = v; stack.push(u); } });
      }
      for (var k = order.length - 1; k >= 0; k--) {
        var w = order[k], s = ix.subAt[w] ? subSize(ix.subAt[w].s) : 1;
        if (!ix.subAt[w]) ix.adj[w].forEach(function (u) { if (u !== parent[w] && !ix.skip[u] && parent[u] === w) s += side[u]; });
        side[w] = s;
      }
    })();
    function macro(v, parent, key) {
      count++;
      var node = { key: key, type: "macro", v: v, label: ix.label[v] || "", size: side[v], children: [], open: false };
      var nbrs = ix.adj[v].filter(function (u) { return u !== parent && !ix.skip[u]; });
      if (!nbrs.length) return node;
      if (key !== "m" + root && !isOpen(key)) { node.box = true; return node; }
      node.open = true;
      nbrs.forEach(function (u) {
        if (count > limit) return;
        if (ix.subAt[u]) node.children.push(subNode(ix.subAt[u].s, key + "/s" + u, ix.subAt[u].what));
        else node.children.push(macro(u, v, "m" + u));
      });
      return node;
    }
    function subNode(s, key, what) {
      count++;
      var node = { key: key, type: "sub", s: s, label: subLabel(s), what: what || "", size: subSize(s), children: [], open: false };
      if (s.kind === "leaf") return node;
      if (!isOpen(key)) { node.box = true; return node; }
      node.open = true;
      subChildren(s).forEach(function (c, i) { if (count <= limit) node.children.push(subNode(c, key + "." + i)); });
      return node;
    }
    var tree = macro(root, -1, "m" + root);
    return { tree: tree, count: count, truncated: count > limit };
  }

  /** Exact states of the expanded parts of the clocks: they are simulated with
   * the majority rule, with their attachment vertex following the macrocell
   * run and every folded subtree following the history of its root. Also
   * checks every simulated vertex against its proven history. */
  function exploreRun(ix, view, Tmax) {
    var g = new Graph(false), gid = {}, forcedMacro = {}, events = new Set(), run = ix.run, simulated = [];
    function addEvents(list) { list.forEach(function (c) { if (c <= Tmax + 1) { events.add(c); events.add(c + 1); } }); }
    function macroVertex(v) {
      if (forcedMacro[v] !== undefined) return forcedMacro[v];
      var x = g.add(stateAt(run.res, v, 0), "macro");
      g.force(x, function (t) { return stateAt(run.res, v, t); });
      addEvents(run.res.changes[v] || []);
      forcedMacro[v] = x;
      return x;
    }
    function walkSub(node, parentVertex) {
      var s = node.s, x;
      if (node.box) {
        x = g.add(subValue(s, 0), "box");
        g.force(x, function (t) { return subValue(s, t); });
        addEvents(subChanges(s));
      } else {
        x = g.add(subValue(s, 0), s.kind);
        simulated.push({ key: node.key, s: s, x: x });
      }
      g.link(parentVertex, x);
      gid[node.key] = x;
      node.children.forEach(function (c) { walkSub(c, x); });
    }
    (function walkMacro(node) {
      node.children.forEach(function (c) {
        if (c.type === "sub") walkSub(c, macroVertex(node.v));
        else walkMacro(c);
      });
    })(view.tree);
    var res = simulate(g, Tmax, { events: Array.from(events).sort(function (a, b) { return a - b; }) });
    var mismatches = 0;
    simulated.forEach(function (o) {
      var want = subChanges(o.s).filter(function (c) { return c <= Tmax; }), got = res.changes[o.x] || [];
      if (res.start[o.x] !== subValue(o.s, 0) || want.length !== got.length || want.some(function (c, i) { return c !== got[i]; })) mismatches++;
    });
    return { res: res, gid: gid, simulated: simulated.length, mismatches: mismatches };
  }

  // ------------------------------------------------------------ demos
  /** One macrocell A - C - B with leaves on A and B (5 vertices). */
  function macrocell(g, b, prefix) {
    var A = g.add(b, prefix + "A"), C = g.add(b, prefix + "C"), B = g.add(b, prefix + "B");
    var a = g.add(b, prefix + "A'"), bb = g.add(b, prefix + "B'");
    g.link(A, C); g.link(C, B); g.link(A, a); g.link(B, bb);
    return { A: A, C: C, B: B, a: a, b: bb };
  }
  /** Controls of a main vertex as two forced vertices following u(t). */
  function controls(g, v, u) {
    var out = [];
    for (var j = 1; j <= 2; j++) {
      var e = g.add(j <= u(0) ? 1 : 0, "control");
      g.link(v, e);
      g.force(e, (function (jj) { return function (t) { return jj <= u(t) ? 1 : 0; }; })(j));
      out.push(e);
    }
    return out;
  }

  /** A lone macrocell under a mode schedule, with forced ports.
   * scenario: "hold" | "reset" | "load" | "copy"; opts: init (5 bits for
   * A, C, B, A', B'), ports ({A, C, B} -> function or array), seed. */
  function macroDemo(scenario, opts) {
    opts = opts || {};
    var g = new Graph(false), init = opts.init || [0, 0, 0, 0, 0];
    var m = { A: g.add(init[0], "A"), C: g.add(init[1], "C"), B: g.add(init[2], "B"), a: g.add(init[3], "leaf"), b: g.add(init[4], "leaf") };
    g.link(m.A, m.C); g.link(m.C, m.B); g.link(m.A, m.a); g.link(m.B, m.b);
    var len = scenario === "hold" ? 0 : scenario === "copy" ? 8 : 4;
    var u = function (t) {
      if (scenario === "hold" || t >= len) return 1;
      if (scenario === "reset") return 0;
      if (scenario === "load") return 2;
      return t < 4 ? 0 : 2;
    };
    var T = opts.T || (scenario === "hold" ? 16 : len + 6);
    var ports = {}, ctrls = {};
    ["A", "C", "B"].forEach(function (X) {
      var seq = opts.ports[X];
      var p = g.add(seqAt(seq, 0), "port");
      g.link(m[X], p);
      g.force(p, seq);
      ports[X] = p;
      ctrls[X] = controls(g, m[X], u);
    });
    return { graph: g, cell: m, ports: ports, controls: ctrls, u: u, T: T, len: len };
  }

  /** Steps of GATE(op) for the demo cells g, cA, cB, rA, rB, b1. */
  function gateSchedule(op) {
    var ci = { g: 0, cA: 1, cB: 2, rA: 3, rB: 4, b1: 5 };
    var P = new Program(ci);
    P.gate(op);
    return { steps: P.steps, tree: P.root.children[0], cells: ["g", "cA", "cB", "rA", "rB", "b1"] };
  }

  /** Macrocell g with its operand arms and the bus neighbour b1, wired as in
   * the reduction; the temporaries hold A and B; GATE(op) runs after "lead"
   * steps of HOLD and is followed by "tail" steps of HOLD. */
  function gateDemo(op, A, B, lead, tail) {
    lead = lead === undefined ? 2 : lead; tail = tail === undefined ? 4 : tail;
    var sch = gateSchedule(op), g = new Graph(false), cells = {};
    var init = { g: 0, cA: 0, cB: 0, rA: A ? 1 : 0, rB: B ? 1 : 0, b1: 0 };
    sch.cells.forEach(function (name) { cells[name] = macrocell(g, init[name], name + "."); });
    var mode = function (c, t) {
      var s = t - lead;
      if (s < 0 || s >= sch.steps.length) return HOLD;
      var e = sch.steps[s].filter(function (x) { return x[0] === c; })[0];
      return e ? [e[1], e[2], e[3]] : HOLD;
    };
    var ctrls = {};
    sch.cells.forEach(function (name, c) {
      ctrls[name] = {};
      ["A", "C", "B"].forEach(function (X, xi) {
        ctrls[name][X] = controls(g, cells[name][X], function (t) { return mode(c, t)[xi]; });
      });
    });
    var wires = [["g", "A", "cA", "A"], ["g", "B", "cB", "A"], ["g", "C", "b1", "A"], ["cA", "B", "rA", "A"], ["cB", "B", "rB", "A"]];
    var used = {};
    wires.forEach(function (w) { g.link(cells[w[0]][w[1]], cells[w[2]][w[3]]); used[w[0] + w[1]] = used[w[2] + w[3]] = 1; });
    var cherries = {};
    sch.cells.forEach(function (name) {
      ["A", "C", "B"].forEach(function (X) {
        if (!used[name + X]) { var c = cherry(g, 0); g.link(cells[name][X], c.port); cherries[name + X] = c.port; }
      });
    });
    var phases = [], t0 = lead;
    sch.tree.children.forEach(function (ph) { phases.push({ name: ph.name, start: t0 + ph.start, len: ph.len }); });
    return {
      graph: g, cells: cells, controls: ctrls, cherries: cherries, wires: wires, mode: mode, lead: lead,
      T: lead + sch.steps.length + tail, phases: phases, result: op === "and" ? (A & B) : (A | B), gateEnd: lead + sch.steps.length
    };
  }

  // ------------------------------------------------------------ exports
  var api = {
    S_of: S_of, Hist: Hist, wordHist: wordHist, wordValue: wordValue,
    Graph: Graph, cherry: cherry, timer: timer, pulse: pulse, generator: generator,
    timerSize: timerSize, pulseSize: pulseSize, generatorSize: generatorSize, generatorShape: generatorShape,
    compile: compile, simulate: simulate, stateAt: stateAt, consumer: consumer, mulberry32: mulberry32,
    validate: validate, evaluate: evaluate, lower: lower, toMcvp: toMcvp, inputBits: inputBits,
    mcvpValues: mcvpValues, cellNames: cellNames, portAssignment: portAssignment, plan: plan,
    uAt: uAt, physIdx: physIdx, controlHist: controlHist, controlWord: controlWord, treeSize: treeSize,
    macroGraph: macroGraph, controlEvents: controlEvents, runMacro: runMacro,
    expectedCells: expectedCells, checkRun: checkRun, HOLD: HOLD, RESET: RESET, LOAD: LOAD,
    macrocell: macrocell, macroDemo: macroDemo, gateSchedule: gateSchedule, gateDemo: gateDemo,
    sub: sub, subOfHist: subOfHist, subValue: subValue, subChanges: subChanges, subChildren: subChildren,
    subSize: subSize, subLabel: subLabel, fullIndex: fullIndex, explore: explore, exploreRun: exploreRun
  };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else scope.MajorityTree = api;
})(typeof window !== "undefined" ? window : this);
