/* Majority on trees — "Gadgets" tab.
 * Every gadget is built by MajorityTree (assets/tree-model.js) and simulated
 * exactly: each frame is the state of every vertex under synchronous
 * majority. A dashed vertex follows a forced history (the consumer of a
 * clock, or the ports and controls of a lone macrocell).
 */
(function () {
  "use strict";

  var MT = window.MajorityTree, TD = window.TreeDraw, CONFIG = window.SITE_CONFIG || {};
  if (!MT || !TD) return;
  var $ = function (s, r) { return (r || document).querySelector(s); };
  var params = new URLSearchParams(window.location.search);
  var isEmbed = params.has("embed");

  var el = {
    list: $("#gadget-list"), title: $("#g-title"), fn: $("#g-fn"), params: $("#g-params"),
    stage: $("#stage"), wrap: $("#tv-svg-wrap"), strips: $("#g-strips"), slider: $("#time-slider"),
    ticks: $("#ticks"), badge: $("#time-badge"), play: $("#btn-play"), first: $("#btn-first"),
    prev: $("#btn-prev"), next: $("#btn-next"), last: $("#btn-last"), speed: $("#speed"),
    text: $("#g-text"), reading: $("#g-reading"), readout: $("#readout"), dlJson: $("#g-dl-json"),
    dlEdges: $("#g-dl-edges"), live: $("#live"), credit: $("#embed-credit")
  };

  var CONSUMERS = [["anti", "adversarial (votes against the next bit)"], ["rand", "random"], ["zeros", "always 0"],
    ["ones", "always 1"], ["lag", "against the current bit"]];
  function consumerParam() { return { key: "consumer", label: "Consumer", type: "select", options: CONSUMERS, def: "anti" }; }
  var BITS01 = [["1", "1"], ["0", "0"]];

  // ---------------------------------------------------------------- helpers
  function range(n) { var a = []; for (var i = 0; i < n; i++) a.push(i); return a; }
  function adjacency(g) {
    var nb = g.st.map(function () { return []; });
    for (var k = 0; k < g.au.length; k += 2) { nb[g.au[k]].push(g.av[k]); nb[g.av[k]].push(g.au[k]); }
    return nb;
  }
  function addConsumer(g, port, kind, expected) {
    var e = g.add(0, "consumer");
    g.link(port, e);
    g.force(e, MT.consumer(kind, expected, 12345));
    return e;
  }
  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; });
  }
  function bit(b) { return '<span class="bit ' + (b ? "one" : "zero") + '">' + (b ? 1 : 0) + "</span>"; }
  function sub(s) { return String(s).replace(/(\d+)/g, "<sub>$1</sub>"); }
  function timerLabel(T) { return (T.rising ? "U" : "D") + T.tau; }
  function parseBits(s, maxLen) {
    var w = String(s || "").replace(/[^01]/g, "").slice(0, maxLen).split("").map(Number);
    if (w.length < 2) throw new Error("Enter a word of at least two bits (0 and 1).");
    return w;
  }

  /** A port that must follow `expected`; rows for the strips and the readout. */
  function clockModel(g, port, consumer, expected, T, extra) {
    var res = MT.simulate(g, T, { frames: true });
    var at = function (v, t) { return res.frames[Math.min(t, T)][v]; };
    var ok = expected.every(function (b, t) { return at(port, t) === b; });
    return Object.assign({
      graph: g, res: res, T: T, port: port,
      strips: [
        { label: "target", bits: function (t) { return expected[t]; }, cls: "target" },
        { label: "port", bits: function (t) { return at(port, t); } },
        { label: "consumer", bits: function (t) { return at(consumer, t); }, cls: "forced" }
      ],
      readout: function (t) {
        return "<caption>At t = " + t + "</caption><tbody>" +
          "<tr><td>target</td><td>" + bit(expected[t]) + "</td></tr>" +
          "<tr><td>port</td><td>" + bit(at(port, t)) + "</td></tr>" +
          "<tr><td>consumer</td><td>" + bit(at(consumer, t)) + "</td></tr></tbody>";
      },
      reading: ok ? "The port follows its target at every step, against this consumer." :
        "The port differs from its target: this should not happen.",
      verdictOk: ok
    }, extra || {});
  }

  // ---------------------------------------------------------------- gadgets
  function buildConstant(v) {
    var g = new MT.Graph(false), b = Number(v.value);
    var C = MT.cherry(g, b), T = 10;
    var exp = range(T + 1).map(function () { return b; });
    var e = addConsumer(g, C.port, v.consumer, exp);
    var nb = adjacency(g), lv = nb[C.port].filter(function (x) { return x !== e; });
    var scene = {
      nodes: [
        { key: "r", v: C.port, x: 0, y: 0, r: 0.42, cls: "sup port" },
        { key: "l1", v: lv[0], x: -0.9, y: 1.25, r: 0.3, cls: "sup" },
        { key: "l2", v: lv[1], x: 0.9, y: 1.25, r: 0.3, cls: "sup" },
        { key: "e", v: e, x: 0, y: -1.45, r: 0.36, cls: "sig forced", title: "consumer (forced)" }
      ],
      edges: [{ a: "r", b: "l1" }, { a: "r", b: "l2" }, { a: "r", b: "e", cls: "consumer" }],
      texts: [{ x: 0.75, y: -1.42, text: "consumer", anchor: "start", cls: "muted" }]
    };
    return clockModel(g, C.port, e, exp, T, {
      scene: scene,
      text: "A cherry: a root and two leaves, all in state b. The leaves copy the root, and the root sees two votes b " +
        "out of three, so the three vertices keep b forever, whatever the consumer does. Every constant of the " +
        "construction is a private cherry; no vertex is fixed from outside."
    });
  }

  function buildTimer(v) {
    var tau = Number(v.tau), up = v.dir === "up";
    var g = new MT.Graph(false), Tm = MT.timer(g, tau, up), T = tau + 4;
    var exp = range(T + 1).map(function (t) { return (t >= tau) === up ? 1 : 0; });
    var e = addConsumer(g, Tm.port, v.consumer, exp);
    var nb = adjacency(g), nodes = [], edges = [], X = 1.15;
    nodes.push({ key: "r", v: Tm.port, x: 0, y: 0, r: 0.42, cls: "sig port", title: "port r" });
    nodes.push({ key: "e", v: e, x: 0, y: -1.5, r: 0.36, cls: "sig forced", title: "consumer (forced)" });
    edges.push({ a: "r", b: "e", cls: "consumer" });
    Tm.arms.forEach(function (arm, k) {
      var sgn = k === 0 ? -1 : 1, prev = "r";
      arm.nodes.forEach(function (n, i) {
        var x = sgn * (i + 1) * X, key = "v" + k + "_" + i, ck = "c" + k + "_" + i;
        nodes.push({ key: key, v: n.v, x: x, y: 0, r: 0.36, cls: "sig", label: String(i + 1), fs: 0.3, title: "v" + (i + 1) });
        nodes.push({ key: ck, v: n.c, x: x, y: 1.1, r: 0.27, cls: "sup" });
        nb[n.c].filter(function (z) { return z !== n.v; }).forEach(function (lf, j) {
          nodes.push({ key: ck + "l" + j, v: lf, x: x + (j ? 0.27 : -0.27), y: 1.72, r: 0.15, cls: "sup" });
          edges.push({ a: ck, b: ck + "l" + j });
        });
        edges.push({ a: prev, b: key }); edges.push({ a: key, b: ck });
        prev = key;
      });
      var ax = sgn * (arm.nodes.length + 1) * X, ak = "a" + k;
      nodes.push({ key: ak, v: arm.end, x: ax, y: 0, r: 0.34, cls: "sup", label: "a", fs: 0.3 });
      edges.push({ a: prev, b: ak });
      var from = arm.nodes.length ? arm.nodes[arm.nodes.length - 1].v : Tm.port;
      nb[arm.end].filter(function (z) { return z !== from; }).forEach(function (lf, j) {
        nodes.push({ key: ak + "l" + j, v: lf, x: ax + sgn * 0.6, y: j ? 0.45 : -0.45, r: 0.15, cls: "sup" });
        edges.push({ a: ak, b: ak + "l" + j });
      });
    });
    return clockModel(g, Tm.port, e, exp, T, {
      scene: scene(nodes, edges),
      ticks: [{ t: tau, label: "τ" }],
      text: "Two identical arms r – v1 – … – vL – a, with L = τ − 1. Every vᵢ hangs a constant-" + (up ? "1" : "0") +
        " cherry, so it computes the " + (up ? "OR" : "AND") + " of its two path neighbours; the end a is a constant. " +
        "The " + (up ? "1" : "0") + " at the ends travels one step per vertex and reaches r at τ. The two arms always " +
        "agree, so their two votes beat the consumer. Size 8τ − 1, degree 3."
    });
  }

  function buildPulse(v) {
    var a = Number(v.a), b = Number(v.b), neg = v.sign === "neg";
    if (!(a < b)) throw new Error("A pulse needs a < b.");
    var g = new MT.Graph(false), P = MT.pulse(g, a, b, neg), T = b + 3;
    var exp = range(T + 1).map(function (t) { return ((a <= t && t < b) !== neg) ? 1 : 0; });
    var e = addConsumer(g, P.port, v.consumer, exp);
    var nodes = [], edges = [], Y = 2.3;
    nodes.push({ key: "e", v: e, x: 0, y: -1.7, r: 0.36, cls: "sig forced", title: "consumer (forced)" });
    P.levels.forEach(function (lev, l) {
      var y = l * Y, rk = "p" + l;
      nodes.push({ key: rk, v: lev.root, x: 0, y: y, r: 0.42, cls: "sig" + (l === 0 ? " port" : ""),
        title: "pulse root, level " + l + ": P[" + lev.a + "," + lev.b + ")" });
      edges.push({ a: l === 0 ? "e" : "p" + (l - 1), b: rk, cls: l === 0 ? "consumer" : "" });
      lev.D.forEach(function (D, i) {
        var k = rk + "D" + i, x = -3.0, yy = y + (lev.D.length > 1 ? (i ? 0.55 : -0.55) : 0);
        nodes.push({ key: k, v: D.port, x: x, y: yy, shape: "box", w: 2.1, h: 0.82, cls: "sig clock", label: timerLabel(D),
          title: "timer " + timerLabel(D) + " (" + D.size + " vertices)" });
        edges.push({ a: rk, b: k });
      });
      var zk = rk + "z";
      nodes.push({ key: zk, v: lev.zero.port, x: -0.95, y: y + 1.05, r: 0.3, cls: "sup", label: String(lev.zero.value), fs: 0.3, title: "constant" });
      edges.push({ a: rk, b: zk });
      var tk = rk + "t", third = lev.third;
      if (third.kind === "timer") nodes.push({ key: tk, v: third.port, x: 3.0, y: y, shape: "box", w: 2.1, h: 0.82, cls: "sig clock", label: timerLabel(third), title: "timer " + timerLabel(third) });
      else nodes.push({ key: tk, v: third.port, x: 0.95, y: y + 1.05, r: 0.3, cls: "sup", label: String(third.value), fs: 0.3, title: "constant" });
      edges.push({ a: rk, b: tk });
    });
    var texts = P.levels.map(function (lev, l) {
      return { x: 1.25, y: l * Y - 0.55, text: (neg ? "¬" : "") + "P[" + lev.a + "," + lev.b + ")", anchor: "start", cls: "muted" };
    });
    return clockModel(g, P.port, e, exp, T, {
      scene: scene(nodes, edges, texts),
      ticks: [{ t: a, label: "a" }, { t: b, label: "b" }],
      text: "P[a,b) is 1 exactly for a ≤ t < b. Its port has four children: a timer D falling at b − 1, the constant 0, " +
        "a timer U rising at a − 1 and the pulse P[a − 1, b − 1); the last level uses D, 0, 1 and a second D. At every " +
        "step three children agree with the next bit, so the port (degree 5) follows the pulse whatever the consumer " +
        "does. Each timer box is a full two-arm timer; its color is its port. Complementing every state gives ¬P."
    });
  }

  function genModel(v, kind) {
    var w = parseBits(v.word, kind === "dissident" ? 16 : 14);
    var H = w.length - 1, S = MT.S_of(H), h = MT.wordHist(w);
    var g = new MT.Graph(true), G = MT.generator(g, h), T = S + H + 4;
    var exp = range(T + 1).map(function (t) { return MT.wordValue(w, t); });
    var e = addConsumer(g, G.port, v.consumer, exp);
    var res = MT.simulate(g, T, { frames: true });
    return { w: w, H: H, S: S, h: h, g: g, G: G, T: T, exp: exp, e: e, res: res };
  }

  function baseLabel(n) {
    if (n.kind === "const") return String(n.value);
    if (n.kind === "timer") return timerLabel(n);
    return (n.neg ? "¬P" : "P") + "[" + n.a + "," + n.b + ")";
  }

  function buildDissident(v) {
    var m = genModel(v, "dissident"), G = m.G, h = m.h;
    if (G.kind !== "node") throw new Error("This word has at most two changes, so its generator is a single " +
      baseLabel(G).replace(/\[.*/, "") + ": choose a word with three changes or more.");
    var at = function (x, t) { return m.res.frames[Math.min(t, m.T)][x]; };
    var nodes = [
      { key: "r", v: G.port, x: 0, y: 0, r: 0.5, cls: "sig port", title: "node r (degree 5)" },
      { key: "e", v: m.e, x: 0, y: -1.7, r: 0.38, cls: "sig forced", title: "consumer (forced)" }
    ], edges = [{ a: "r", b: "e", cls: "consumer" }], texts = [];
    G.children.forEach(function (c, j) {
      var x = (j - 1.5) * 3.2, k = "c" + j;
      nodes.push({ key: k, v: c.port, x: x, y: 2.6, shape: "box", w: 2.7, h: 1.0, cls: "sig clock", label: "child " + j,
        title: "generator of h_" + j + ": " + c.hist.K() + " changes" });
      edges.push({ a: "r", b: k });
      texts.push({ x: x, y: 3.55, text: c.hist.K() + " changes", cls: "muted", fs: 0.34 });
      texts.push({ x: x, y: 1.75, text: "", key: "mark" + j, cls: "mark", fs: 0.36 });
    });
    texts.push({ x: 0.85, y: -0.25, text: "", key: "votes", anchor: "start", cls: "muted", fs: 0.36 });
    var rows = [{ label: "h (target)", bits: function (t) { return m.exp[t]; }, cls: "target" },
      { label: "node r", bits: function (t) { return at(G.port, t); } }];
    G.children.forEach(function (c, j) { rows.push({ label: "child " + j, bits: function (t) { return at(c.port, t); } }); });
    rows.push({ label: "consumer", bits: function (t) { return at(m.e, t); }, cls: "forced" });
    var ok = m.exp.every(function (b, t) { return at(G.port, t) === b; });
    return {
      graph: m.g, res: m.res, T: m.T, scene: scene(nodes, edges, texts), strips: rows,
      ticks: [{ t: m.S, label: "S" }],
      textOf: function (key, t) {
        var next = h.at(t + 1), d = h.dissident(t);
        if (key === "votes") {
          var agree = G.children.filter(function (c) { return at(c.port, t) === next; }).length;
          return agree + " of 4 children vote " + next;
        }
        if (key.indexOf("mark") === 0) return Number(key.slice(4)) === d ? "dissident" : "";
        return undefined;
      },
      readout: function (t) {
        var next = h.at(t + 1);
        return "<caption>At t = " + t + " (next bit " + next + ")</caption><thead><tr><th>child</th><th>port</th><th>changes</th></tr></thead><tbody>" +
          G.children.map(function (c, j) {
            return "<tr><td>" + j + (j === h.dissident(t) ? " (dissident)" : "") + "</td><td>" + bit(at(c.port, t)) + "</td><td>" + c.hist.K() + "</td></tr>";
          }).join("") + "</tbody>";
      },
      text: "The node r of a word generator has four children and its consumer. Child j plays h_j(t) = h(t+1) ⊕ [j ≡ q(t+1) mod 4], " +
        "where q counts the changes of h: three children always show the next bit, so r (degree 5) follows h whatever the " +
        "consumer does. When h changes, the old dissident already has the new value, the new one keeps the old value, and " +
        "only two children change: each child inherits about half of the " + h.K() + " changes.",
      reading: ok ? "The node follows its word at every step; the word is played after the common delay S = " + m.S + "." :
        "The node differs from its word: this should not happen.",
      verdictOk: ok
    };
  }

  function buildGenerator(v) {
    var m = genModel(v, "generator"), G = m.G;
    var at = function (x, t) { return m.res.frames[Math.min(t, m.T)][x]; };
    var nodes = [{ key: "e", v: m.e, x: 0, y: -1.8, r: 0.38, cls: "sig forced", title: "consumer (forced)" }];
    var edges = [], leafX = 0, DX = 2.5, DY = 2.4;
    function place(n, depth, key) {
      var x;
      if (n.kind === "node") {
        var xs = n.children.map(function (c, j) { return place(c, depth + 1, key + j); });
        x = (xs[0] + xs[xs.length - 1]) / 2;
        nodes.push({ key: key, v: n.port, x: x, y: depth * DY, r: 0.42, cls: "sig" + (depth === 0 ? " port" : ""),
          title: "node: " + n.hist.K() + " changes" });
        n.children.forEach(function (c, j) { edges.push({ a: key, b: key + j }); });
      } else {
        x = leafX; leafX += DX;
        var isConst = n.kind === "const";
        nodes.push({ key: key, v: n.port, x: x, y: depth * DY, shape: isConst ? "circle" : "box", r: 0.32, w: 2.0, h: 0.8,
          cls: isConst ? "sup" : "sig clock", label: baseLabel(n), fs: isConst ? 0.3 : 0.36,
          title: (n.kind === "pulse" ? "pulse" : n.kind) + " " + baseLabel(n) + " (" + n.size + " vertices)" });
      }
      return x;
    }
    var rootX = place(G, 0, "n");
    nodes[0].x = rootX;
    edges.push({ a: "n", b: "e", cls: "consumer" });
    var shape = MT.generatorShape(m.h);
    var ok = m.exp.every(function (b, t) { return at(G.port, t) === b; });
    return {
      graph: m.g, res: m.res, T: m.T, scene: scene(nodes, edges), minUnit: 22,
      strips: [{ label: "word (target)", bits: function (t) { return m.exp[t]; }, cls: "target" },
        { label: "port", bits: function (t) { return at(G.port, t); } },
        { label: "consumer", bits: function (t) { return at(m.e, t); }, cls: "forced" }],
      ticks: [{ t: m.S, label: "S" }, { t: m.S + m.H, label: "S + H" }],
      readout: function (t) {
        return "<caption>Word of " + m.w.length + " bits</caption><tbody>" +
          "<tr><td>changes K</td><td>" + m.h.K() + "</td></tr>" +
          "<tr><td>S = ⌈log₂(H + 2)⌉ + 8</td><td>" + m.S + "</td></tr>" +
          "<tr><td>depth / leaves</td><td>" + shape.depth + " / " + shape.leaves + "</td></tr>" +
          "<tr><td>vertices</td><td>" + G.size.toLocaleString("en-US") + "</td></tr>" +
          "<tr><td>port at t = " + t + "</td><td>" + bit(at(G.port, t)) + "</td></tr></tbody>";
      },
      text: "The full degree-5 generator of the word: nodes with a rotating dissident split the changes among four " +
        "branches until at most two remain; then a constant, a timer or a pulse plays the rest. Each box stands for its " +
        "whole subtree, simulated exactly; its color is its port. The port plays w(0) until S and then w(t − S), whatever " +
        "the consumer does.",
      reading: ok ? "The port plays the word at every step against this consumer (" + G.size.toLocaleString("en-US") + " vertices)." :
        "The port differs from its word: this should not happen.",
      verdictOk: ok
    };
  }

  function buildMacro(v) {
    var mode = v.mode, seed = Number(v.seed) || 1, rnd = MT.mulberry32(seed * 7 + 3), T = mode === "hold" ? 16 : mode === "copy" ? 14 : 10;
    var bits = String(v.bits || "101").replace(/[^01]/g, "").padEnd(3, "0").slice(0, 3).split("").map(Number);
    var init, ports = {}, note;
    var noise = function () { return range(T + 8).map(function () { return rnd() < 0.5 ? 1 : 0; }); };
    if (mode === "hold") {
      init = [bits[0], bits[0], bits[0], bits[0], bits[0]];
      ["A", "C", "B"].forEach(function (X) { ports[X] = noise(); });
      note = "HOLD (u = 1): every main vertex takes the majority of its two memory neighbours and its port. A stored bit " +
        "has two votes in every main vertex, so it survives any port activity.";
    } else if (mode === "reset") {
      init = range(5).map(function () { return rnd() < 0.5 ? 1 : 0; });
      var zero = ["A", "C", "B"][seed % 3];
      ["A", "C", "B"].forEach(function (X) { ports[X] = X === zero ? range(T + 8).map(function () { return 0; }) : noise(); });
      note = "RESET (u = 0 for 4 steps): AND of the three other neighbours. The port " + zero + " stays 0, so the 0 spreads " +
        "along the path and the leaves: the macrocell is cleared from any state, in at most 4 steps, while the other two " +
        "ports do anything. Then HOLD.";
    } else if (mode === "load") {
      init = [0, 0, 0, 0, 0];
      ["A", "C", "B"].forEach(function (X, i) { ports[X] = range(T + 8).map(function () { return bits[i]; }); });
      note = "LOAD (u = 2 for 4 steps) from 0, with constant ports: OR of the three other neighbours, so the macrocell " +
        "becomes the OR of its ports (" + bits.join(", ") + "), leaves included. Then HOLD.";
    } else {
      init = range(5).map(function () { return rnd() < 0.5 ? 1 : 0; });
      var src = ["A", "C", "B"][seed % 3];
      ["A", "C", "B"].forEach(function (X) { ports[X] = range(T + 8).map(function () { return X === src ? bits[0] : 0; }); });
      note = "COPY = RESET for 4 steps, then LOAD for 4 steps, with only port " + src + " possibly 1 (it holds " + bits[0] +
        "): the macrocell ends up storing the bit of that port, from any initial state. Then HOLD.";
    }
    var d = MT.macroDemo(mode, { init: init, ports: ports, T: T });
    var res = MT.simulate(d.graph, d.T, { frames: true });
    var at = function (x, t) { return res.frames[Math.min(t, d.T)][x]; };
    var c = d.cell, nodes = [], edges = [], texts = [];
    var pos = { A: -1.7, C: 0, B: 1.7 };
    ["A", "C", "B"].forEach(function (X) {
      nodes.push({ key: X, v: c[X], x: pos[X], y: 0, r: 0.48, cls: "sig", label: X, fs: 0.4 });
      nodes.push({ key: "p" + X, v: d.ports[X], x: pos[X], y: 1.55, r: 0.3, shape: "square", cls: "sig forced", title: "port " + X + " (forced)" });
      edges.push({ a: X, b: "p" + X, cls: "port-edge" });
      d.controls[X].forEach(function (q, j) {
        var k = "u" + X + j;
        nodes.push({ key: k, v: q, x: pos[X] + (j ? 0.32 : -0.32), y: -1.35, r: 0.2, shape: "square", cls: "sig forced", title: "control " + (j + 1) + " of " + X });
        edges.push({ a: X, b: k, cls: "control" });
      });
    });
    texts.push({ x: 0, y: -2.05, text: "", key: "mode", cls: "mode", fs: 0.36 });
    nodes.push({ key: "a", v: c.a, x: -3.2, y: 0, r: 0.34, cls: "sig", label: "A'", fs: 0.3 });
    nodes.push({ key: "b", v: c.b, x: 3.2, y: 0, r: 0.34, cls: "sig", label: "B'", fs: 0.3 });
    edges.push({ a: "A", b: "C" }, { a: "C", b: "B" }, { a: "A", b: "a" }, { a: "B", b: "b" });
    texts.push({ x: 0, y: 2.35, text: "ports (forced)", cls: "muted", fs: 0.32 });
    var MODE = ["AND", "MAJ", "OR"];
    var expectFinal = mode === "hold" ? bits[0] : mode === "reset" ? 0 : mode === "load" ? (bits.some(Boolean) ? 1 : 0) : bits[0];
    var cells5 = [c.A, c.C, c.B, c.a, c.b];
    var ok = range(d.T - d.len + 1).every(function (k) { return cells5.every(function (x) { return at(x, d.len + k) === expectFinal; }); });
    return {
      graph: d.graph, res: res, T: d.T, scene: scene(nodes, edges, texts),
      strips: [{ label: "A", bits: function (t) { return at(c.A, t); } }, { label: "C", bits: function (t) { return at(c.C, t); } },
        { label: "B", bits: function (t) { return at(c.B, t); } }, { label: "A'", bits: function (t) { return at(c.a, t); } },
        { label: "B'", bits: function (t) { return at(c.b, t); } },
        { label: "port A", bits: function (t) { return at(d.ports.A, t); }, cls: "forced" },
        { label: "port C", bits: function (t) { return at(d.ports.C, t); }, cls: "forced" },
        { label: "port B", bits: function (t) { return at(d.ports.B, t); }, cls: "forced" }],
      ticks: d.len ? [{ t: d.len, label: mode === "copy" ? "8" : "4" }] : [],
      textOf: function (key, t) {
        if (key === "mode") { var u = d.u(t); return "controls in 1: u = " + u + " (" + MODE[u] + " of the three other neighbours)"; }
        return undefined;
      },
      readout: function (t) {
        return "<caption>At t = " + t + "</caption><tbody><tr><td>controls in 1</td><td>" + d.u(t) + " (" + MODE[d.u(t)] + ")</td></tr>" +
          "<tr><td>A C B A' B'</td><td>" + cells5.map(function (x) { return bit(at(x, t)); }).join(" ") + "</td></tr>" +
          "<tr><td>expected from t = " + d.len + "</td><td>" + bit(expectFinal) + "</td></tr></tbody>";
      },
      text: note,
      reading: ok ? "From t = " + d.len + " on, the five vertices hold " + expectFinal + ", as the notes state." :
        "The macrocell did not reach the expected state: this should not happen.",
      verdictOk: ok
    };
  }

  function buildGate(v) {
    var op = v.op, A = Number(v.A), B = Number(v.B);
    var d = MT.gateDemo(op, A, B, 2, 5);
    var res = MT.simulate(d.graph, d.T, { frames: true });
    var at = function (x, t) { return res.frames[Math.min(t, d.T)][x]; };
    var nodes = [], edges = [], texts = [], DXC = 3.6;
    // Left to right: rA (B C A), cA (B C A), g (A C B), cB (A C B), rB (A C B); b1 below g.
    var layout = { rA: { x: -2 * DXC, flip: true }, cA: { x: -DXC, flip: true }, g: { x: 0 }, cB: { x: DXC }, rB: { x: 2 * DXC }, b1: { x: 1.0, y: 3.2 } };
    var MODE = ["AND", "MAJ", "OR"];
    Object.keys(layout).forEach(function (name) {
      var L = layout[name], cx = L.x, cy = L.y || 0, m = d.cells[name], s = L.flip ? -1 : 1;
      var px = { A: cx - s * 1.0, C: cx, B: cx + s * 1.0 };
      if (name === "b1") px = { A: 0, C: 1.0, B: 2.0 };
      ["A", "C", "B"].forEach(function (X) {
        nodes.push({ key: name + X, v: m[X], x: px[X], y: cy, r: 0.36, cls: "sig", label: X, fs: 0.3, title: name + "." + X });
        texts.push({ x: px[X], y: cy - 0.62, text: "", key: "u:" + name + ":" + X, cls: "mode", fs: 0.28 });
      });
      nodes.push({ key: name + "a", v: m.a, x: px.A, y: cy + 0.95, r: 0.24, cls: "sig", title: name + ".A'" });
      nodes.push({ key: name + "b", v: m.b, x: px.B, y: cy + 0.95, r: 0.24, cls: "sig", title: name + ".B'" });
      edges.push({ a: name + "A", b: name + "C" }, { a: name + "C", b: name + "B" }, { a: name + "A", b: name + "a" }, { a: name + "B", b: name + "b" });
      texts.push({ x: name === "b1" ? px.C : cx, y: cy - 1.2, text: name, cls: "cell-name", fs: 0.42 });
      ["A", "C", "B"].forEach(function (X) {
        var ch = d.cherries[name + X];
        if (ch === undefined) return;
        var ox = X === "C" ? 0 : (X === "A" ? -s : s) * 0.75, oy = X === "C" ? 0.95 : 0;
        nodes.push({ key: name + X + "k", v: ch, x: px[X] + ox, y: cy + oy, r: 0.14, cls: "sup cherry", title: "constant-0 cherry on the unused port" });
        edges.push({ a: name + X, b: name + X + "k" });
      });
    });
    d.wires.forEach(function (w) { edges.push({ a: w[0] + w[1], b: w[2] + w[3], cls: "port-edge" }); });
    var phaseAt = function (t) {
      for (var i = d.phases.length - 1; i >= 0; i--) if (t >= d.phases[i].start) return t < d.phases[i].start + d.phases[i].len ? d.phases[i].name : (i === d.phases.length - 1 ? "HOLD: done" : d.phases[i].name);
      return "HOLD (before the gate)";
    };
    var g5 = [d.cells.g.A, d.cells.g.C, d.cells.g.B, d.cells.g.a, d.cells.g.b];
    var ok = g5.every(function (x) { return at(x, d.T) === d.result; });
    return {
      graph: d.graph, res: res, T: d.T, scene: scene(nodes, edges, texts),
      strips: [{ label: "rA", bits: function (t) { return at(d.cells.rA.C, t); } }, { label: "cA", bits: function (t) { return at(d.cells.cA.C, t); } },
        { label: "g.A", bits: function (t) { return at(d.cells.g.A, t); } }, { label: "g.C", bits: function (t) { return at(d.cells.g.C, t); } },
        { label: "g.B", bits: function (t) { return at(d.cells.g.B, t); } }, { label: "cB", bits: function (t) { return at(d.cells.cB.C, t); } },
        { label: "rB", bits: function (t) { return at(d.cells.rB.C, t); } }],
      ticks: d.phases.map(function (p, i) { return { t: p.start, label: String(i) }; }).concat([{ t: d.gateEnd, label: "end" }]),
      textOf: function (key, t) {
        if (key.indexOf("u:") === 0) {
          var parts = key.split(":"), c = d.cells, names = ["g", "cA", "cB", "rA", "rB", "b1"];
          var u = d.mode(names.indexOf(parts[1]), t)[["A", "C", "B"].indexOf(parts[2])];
          return String(u);
        }
        return undefined;
      },
      readout: function (t) {
        return "<caption>At t = " + t + "</caption><tbody><tr><td>phase</td><td class=\"phase\">" + escapeHtml(phaseAt(t)) + "</td></tr>" +
          "<tr><td>g (A C B)</td><td>" + [d.cells.g.A, d.cells.g.C, d.cells.g.B].map(function (x) { return bit(at(x, t)); }).join(" ") + "</td></tr>" +
          "<tr><td>result " + op.toUpperCase() + "(" + A + ", " + B + ")</td><td>" + bit(d.result) + "</td></tr></tbody>";
      },
      text: "The 27 steps of GATE in macrocell g. Phase 0 (16 steps) copies r_A and r_B into the connectors while g is held at 0. " +
        "Phases 1 and 2: the ends of g load A and B, then its centre computes " + (op === "and" ? "the majority of A, B and the 0 of b1, that is A ∧ B" : "the OR of A, B and 0, that is A ∨ B") +
        ". Phase 3 clears both connectors while the centre keeps the result; phases 4 and 5 clean the ends and copy the centre, so g " +
        "is again a quiescent macrocell holding the result. The numbers are the controls in 1 of each vertex.",
      reading: ok ? "At the end, all five vertices of g hold " + op.toUpperCase() + "(" + A + ", " + B + ") = " + d.result + "; r_A and r_B are unchanged." :
        "g does not hold the expected result: this should not happen.",
      verdictOk: ok
    };
  }

  function scene(nodes, edges, texts) { return { nodes: nodes, edges: edges, texts: texts || [] }; }

  var GADGETS = [
    { id: "constant", group: "Clocks", title: "Constant", fn: "cherry", build: buildConstant,
      params: [{ key: "value", label: "Value", type: "select", options: BITS01, def: "1" }, consumerParam()] },
    { id: "timer", group: "Clocks", title: "Timer", fn: "[t ≥ τ] or [t < τ]", build: buildTimer,
      params: [{ key: "tau", label: "Date τ", type: "number", min: 1, max: 14, def: 6 },
        { key: "dir", label: "Kind", type: "select", options: [["up", "U: rises at τ"], ["down", "D: falls at τ"]], def: "up" }, consumerParam()] },
    { id: "pulse", group: "Clocks", title: "Pulse", fn: "P[a,b) = [a ≤ t < b]", build: buildPulse,
      params: [{ key: "a", label: "Start a", type: "number", min: 1, max: 8, def: 3 }, { key: "b", label: "End b", type: "number", min: 2, max: 14, def: 7 },
        { key: "sign", label: "Kind", type: "select", options: [["pos", "pulse"], ["neg", "complement"]], def: "pos" }, consumerParam()] },
    { id: "dissident", group: "Clocks", title: "Rotating dissident", fn: "three of four children vote the next bit", build: buildDissident,
      params: [{ key: "word", label: "Word", type: "bits", maxlen: 16, def: "0011010110" }, consumerParam()] },
    { id: "generator", group: "Clocks", title: "Word generator", fn: "w(0) until S, then w(t − S)", build: buildGenerator,
      params: [{ key: "word", label: "Word", type: "bits", maxlen: 14, def: "01101001011" }, consumerParam()] },
    { id: "macrocell", group: "Memory and program", title: "Macrocell", fn: "A – C – B, degree 5", build: buildMacro,
      params: [{ key: "mode", label: "Mode", type: "select", options: [["hold", "HOLD, noisy ports"], ["reset", "RESET from any state"], ["load", "LOAD the OR of the ports"], ["copy", "COPY one port"]], def: "hold" },
        { key: "bits", label: "Bits", type: "bits", maxlen: 3, def: "101", hint: "HOLD and COPY use the first bit; LOAD uses the three port values" },
        { key: "seed", label: "Seed", type: "number", min: 1, max: 99, def: 1 }] },
    { id: "gate", group: "Memory and program", title: "Gate", fn: "27 steps in macrocell g", build: buildGate,
      params: [{ key: "op", label: "Gate", type: "select", options: [["and", "AND"], ["or", "OR"]], def: "and" },
        { key: "A", label: "r_A", type: "select", options: BITS01, def: "1" }, { key: "B", label: "r_B", type: "select", options: BITS01, def: "0" }] }
  ];
  var byId = {};
  GADGETS.forEach(function (g) { byId[g.id] = g; });

  // ---------------------------------------------------------------- state
  var state = { g: null, values: {}, model: null, drawer: null, strips: null, t: 0, playing: null, speed: 2 };

  function buildList() {
    var html = "", group = null;
    GADGETS.forEach(function (g) {
      if (g.group !== group) { group = g.group; html += '<li class="g-group">' + escapeHtml(group) + "</li>"; }
      html += '<li><button type="button" class="gadget-btn" data-gadget="' + g.id + '"><span><span class="g-title">' +
        escapeHtml(g.title) + '</span><span class="g-fn">' + escapeHtml(g.fn) + "</span></span></button></li>";
    });
    el.list.innerHTML = html;
    el.list.addEventListener("click", function (e) {
      var b = e.target.closest("[data-gadget]");
      if (b) select(b.dataset.gadget, true);
    });
  }

  function renderParams() {
    var g = state.g;
    el.params.innerHTML = g.params.map(function (p) {
      var v = state.values[p.key], id = "gp-" + p.key, ctl;
      if (p.type === "select") {
        ctl = '<select id="' + id + '" data-param="' + p.key + '">' + p.options.map(function (o) {
          return '<option value="' + escapeHtml(o[0]) + '"' + (String(v) === o[0] ? " selected" : "") + ">" + escapeHtml(o[1]) + "</option>";
        }).join("") + "</select>";
      } else if (p.type === "number") {
        ctl = '<input id="' + id + '" data-param="' + p.key + '" type="number" min="' + p.min + '" max="' + p.max + '" value="' + escapeHtml(v) + '">';
      } else {
        ctl = '<input id="' + id + '" data-param="' + p.key + '" type="text" inputmode="numeric" spellcheck="false" maxlength="' + p.maxlen +
          '" value="' + escapeHtml(v) + '" class="tv-bits"' + (p.hint ? ' title="' + escapeHtml(p.hint) + '"' : "") + ">";
      }
      return '<label class="tv-param" for="' + id + '"><span>' + escapeHtml(p.label) + "</span>" + ctl + "</label>";
    }).join("") + '<p id="g-error" class="cx-error" role="alert" hidden></p>';
  }

  function select(id, user) {
    var g = byId[id] || GADGETS[0];
    stop();
    state.g = g;
    state.values = {};
    g.params.forEach(function (p) { state.values[p.key] = p.def; });
    el.list.querySelectorAll("[data-gadget]").forEach(function (b) { b.setAttribute("aria-current", String(b.dataset.gadget === g.id)); });
    el.title.textContent = g.title;
    el.fn.textContent = g.fn;
    renderParams();
    rebuild(true);
    if (user && !isEmbed) { try { window.history.replaceState(null, "", "#gadget=" + g.id); } catch (e) { /* ignore */ } }
  }

  function rebuild(reset) {
    var errBox = $("#g-error");
    var model;
    try {
      model = state.g.build(state.values);
      if (errBox) errBox.hidden = true;
    } catch (err) {
      if (errBox) { errBox.textContent = err.message; errBox.hidden = false; }
      return;
    }
    stop();
    state.model = model;
    state.drawer = TD.render(el.wrap, model.scene, { maxWidth: Math.max(320, el.stage.clientWidth - 24), unit: 36, minUnit: model.minUnit || 10, label: state.g.title });
    state.strips = TD.strips(el.strips, model.strips || [], model.T, { label: state.g.title + " histories" });
    el.slider.max = String(model.T);
    el.text.textContent = model.text || "";
    el.reading.textContent = model.reading || "";
    el.reading.classList.toggle("bad", model.verdictOk === false);
    buildTicks();
    setTime(reset ? 0 : Math.min(state.t, model.T));
  }

  function buildTicks() {
    var m = state.model;
    el.ticks.innerHTML = "";
    if (!m || !m.ticks) return;
    m.ticks.forEach(function (tk) {
      var s = document.createElement("span");
      s.className = "tick";
      s.style.left = (100 * tk.t / Math.max(1, m.T)) + "%";
      s.textContent = tk.label;
      el.ticks.appendChild(s);
    });
  }

  function setTime(t) {
    var m = state.model;
    if (!m) return;
    t = Math.max(0, Math.min(m.T, t));
    state.t = t;
    el.slider.value = String(t);
    el.badge.textContent = "t = " + t;
    state.drawer.update(function (n) {
      if (n.v === undefined || n.v === null) return null;
      return m.res.frames[Math.min(t, m.T)][n.v];
    }, m.textOf ? function (key) { return m.textOf(key, t); } : null);
    state.strips.update(t);
    el.readout.innerHTML = m.readout ? m.readout(t) : "";
  }

  function step(d) { stop(); setTime(state.t + d); }
  function play() {
    var m = state.model;
    if (!m) return;
    if (state.t >= m.T) setTime(0);
    el.play.textContent = "Pause";
    el.play.setAttribute("aria-label", "Pause");
    state.playing = window.setInterval(function () {
      if (state.t >= state.model.T) { stop(); return; }
      setTime(state.t + 1);
    }, Math.round(1200 / (state.speed + 1)));
  }
  function stop() {
    if (state.playing) { window.clearInterval(state.playing); state.playing = null; }
    el.play.textContent = "Play";
    el.play.setAttribute("aria-label", "Play");
  }

  // ---------------------------------------------------------------- downloads
  function treeExport() {
    var m = state.model, g = m.graph, verts = [], edges = [], forced = [];
    var isForced = new Set(g.forced.map(function (f) { return f.v; }));
    g.st.forEach(function (s, i) { verts.push({ id: i, state: s, role: g.role[i] || "" }); });
    for (var k = 0; k < g.au.length; k += 2) edges.push(g.aw[k] > 1 ? [g.au[k], g.av[k], g.aw[k]] : [g.au[k], g.av[k]]);
    g.forced.forEach(function (f) {
      forced.push({ vertex: f.v, history: range(m.T + 1).map(function (t) { return typeof f.seq === "function" ? f.seq(t) : f.seq[Math.min(t, f.seq.length - 1)]; }) });
    });
    return {
      gadget: state.g.id, parameters: state.values, rule: "synchronous majority of neighbours, ties keep the state",
      vertices: verts, edges: edges, forced: forced, steps: m.T, compressed: g.compress,
      note: g.compress ? "An edge [u, v, k] means that u counts v k times: k identical private subtrees hang from u and only one is listed. They evolve identically." :
        "Every vertex and edge of the tree. Forced vertices follow the given history instead of the rule.",
      forcedVertices: Array.from(isForced)
    };
  }
  function saveFile(name, parts, type) {
    var a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob(parts, { type: type }));
    a.download = name;
    document.body.appendChild(a);
    a.click();
    window.setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  }
  function dlJson() {
    saveFile("majority-tree-" + state.g.id + ".json", [JSON.stringify(treeExport())], "application/json");
  }
  function dlEdges() {
    var x = treeExport(), lines = [
      "# Majority on trees: gadget " + x.gadget + " " + JSON.stringify(x.parameters),
      "# Rule: " + x.rule + ".",
      "# " + x.note,
      "# vertices " + x.vertices.length + ", edges " + x.edges.length,
      "# initial states (vertex: state): " + x.vertices.map(function (v) { return v.id + ":" + v.state; }).join(" ")
    ];
    x.forced.forEach(function (f) { lines.push("# forced " + f.vertex + ": " + f.history.join("")); });
    x.edges.forEach(function (e) { lines.push(e.join(" ")); });
    saveFile("majority-tree-" + x.gadget + ".txt", [lines.join("\n") + "\n"], "text/plain");
  }

  // ---------------------------------------------------------------- theme
  function initTheme() {
    var btn = $("#theme-toggle");
    var current = function () {
      var a = document.documentElement.getAttribute("data-theme");
      if (a) return a;
      return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
    };
    var label = function () { if (btn) btn.textContent = current() === "dark" ? "Light mode" : "Dark mode"; };
    label();
    if (btn) btn.addEventListener("click", function () {
      var next = current() === "dark" ? "light" : "dark";
      document.documentElement.setAttribute("data-theme", next);
      try { window.localStorage.setItem("mt-theme", next); } catch (e) { /* ignore */ }
      label();
    });
    if (window.matchMedia) {
      var mq = window.matchMedia("(prefers-color-scheme: dark)");
      if (mq.addEventListener) mq.addEventListener("change", label);
    }
  }
  function initLinks() {
    [["#link-notes", CONFIG.notesUrl], ["#link-code", CONFIG.codeUrl]].forEach(function (pair) {
      var a = $(pair[0]);
      if (!a) return;
      if (pair[1]) { a.href = pair[1]; a.hidden = false; } else a.hidden = true;
    });
    if (el.credit) {
      var home = CONFIG.siteUrl || "./";
      el.credit.innerHTML = 'Interactive figure from <a target="_blank" rel="noopener" href="' + escapeHtml(home) + '">Majority on trees</a>.';
    }
  }

  // ---------------------------------------------------------------- events
  function circuitTab() { return document.body.dataset.tab === "circuit"; }
  function initEvents() {
    el.params.addEventListener("change", function (e) {
      var p = e.target.dataset && e.target.dataset.param;
      if (!p) return;
      state.values[p] = e.target.value;
      rebuild(true);
    });
    el.play.addEventListener("click", function () { if (state.playing) stop(); else play(); });
    el.first.addEventListener("click", function () { stop(); setTime(0); });
    el.last.addEventListener("click", function () { stop(); setTime(state.model ? state.model.T : 0); });
    el.prev.addEventListener("click", function () { step(-1); });
    el.next.addEventListener("click", function () { step(1); });
    el.slider.addEventListener("input", function () { stop(); setTime(Number(el.slider.value)); });
    el.speed.addEventListener("change", function () { state.speed = Number(el.speed.value); if (state.playing) { stop(); play(); } });
    el.dlJson.addEventListener("click", dlJson);
    el.dlEdges.addEventListener("click", dlEdges);
    document.addEventListener("keydown", function (e) {
      var tag = (e.target && e.target.tagName) || "";
      if (tag === "INPUT" && e.target.type !== "range") return;
      if (tag === "SELECT" || tag === "TEXTAREA" || e.altKey || e.ctrlKey || e.metaKey || circuitTab()) return;
      if (e.key === "ArrowRight") { step(1); e.preventDefault(); }
      else if (e.key === "ArrowLeft") { step(-1); e.preventDefault(); }
      else if (e.key === " " && tag !== "BUTTON") { if (state.playing) stop(); else play(); e.preventDefault(); }
      else if (e.key === "Home") { stop(); setTime(0); e.preventDefault(); }
      else if (e.key === "End") { stop(); setTime(state.model ? state.model.T : 0); e.preventDefault(); }
    });
    var resizeTimer = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(function () { if (state.model && !circuitTab()) rebuild(false); }, 120);
    });
  }

  // Read-only hook used by the automated browser tests.
  window.MajorityTreeGadgets = { state: state, gadgets: GADGETS, select: select, setTime: setTime, treeExport: treeExport };

  // ---------------------------------------------------------------- boot
  if (isEmbed) document.body.classList.add("embed");
  initTheme();
  initLinks();
  buildList();
  initEvents();
  var fromHash = /^#gadget=([a-z]+)$/.exec(window.location.hash || "");
  select(isEmbed ? params.get("embed") : (fromHash ? fromHash[1] : "pulse"), false);
  if (isEmbed && params.get("autoplay") === "1") play();
})();
