/* Majority on trees — SVG drawing helpers (no dependencies).
 * A scene is {nodes, edges, texts, width, height}; node coordinates are in
 * layout units and scaled to the container. render() returns an object whose
 * update(stateOf, textOf) recolors the nodes for one time step.
 */
(function (scope) {
  "use strict";
  var NS = "http://www.w3.org/2000/svg";

  function el(tag, attrs, parent) {
    var e = document.createElementNS(NS, tag);
    if (attrs) Object.keys(attrs).forEach(function (k) { if (attrs[k] !== undefined && attrs[k] !== null) e.setAttribute(k, attrs[k]); });
    if (parent) parent.appendChild(e);
    return e;
  }

  /**
   * scene.nodes: {key, x, y, r, shape: "circle"|"square"|"box", cls, label,
   *   title, w, h} ; scene.edges: {a, b, cls} (node keys) ;
   * scene.texts: {x, y, text, cls, anchor, key} ; opts.unit (px per unit),
   * opts.maxWidth (px), opts.pad (units).
   */
  function render(container, scene, opts) {
    opts = opts || {};
    container.innerHTML = "";
    var pad = opts.pad === undefined ? 0.8 : opts.pad;
    var xs = [], ys = [];
    scene.nodes.forEach(function (n) {
      var hw = (n.w || 2 * (n.r || 0.3)) / 2, hh = (n.h || 2 * (n.r || 0.3)) / 2;
      xs.push(n.x - hw, n.x + hw); ys.push(n.y - hh, n.y + hh);
    });
    (scene.texts || []).forEach(function (t) { xs.push(t.x); ys.push(t.y); });
    var x0 = Math.min.apply(null, xs) - pad, x1 = Math.max.apply(null, xs) + pad;
    var y0 = Math.min.apply(null, ys) - pad, y1 = Math.max.apply(null, ys) + pad;
    var W = x1 - x0, H = y1 - y0;
    var unit = opts.unit || 34;
    var maxW = opts.maxWidth || container.clientWidth || 800;
    var minUnit = opts.minUnit || 10;
    var u = Math.max(minUnit, Math.min(unit, maxW / W));
    var svg = el("svg", {
      viewBox: [x0, y0, W, H].join(" "), width: Math.round(W * u), height: Math.round(H * u),
      class: "tv-svg", role: "img", "aria-label": opts.label || "Tree"
    }, container);
    var gE = el("g", { class: "tv-edges" }, svg), gN = el("g", { class: "tv-nodes" }, svg), gT = el("g", { class: "tv-texts" }, svg);
    var pos = new Map();
    scene.nodes.forEach(function (n) { pos.set(n.key, n); });
    scene.edges.forEach(function (e) {
      var a = pos.get(e.a), b = pos.get(e.b);
      if (!a || !b) return;
      el("line", { x1: a.x, y1: a.y, x2: b.x, y2: b.y, class: "tv-edge " + (e.cls || "") }, gE);
    });
    var shapes = new Map();
    scene.nodes.forEach(function (n) {
      var g = el("g", { class: "tv-node " + (n.cls || ""), "data-key": n.key }, gN);
      var s;
      if (n.shape === "square") s = el("rect", { x: n.x - n.r, y: n.y - n.r, width: 2 * n.r, height: 2 * n.r, rx: n.r * 0.25 }, g);
      else if (n.shape === "box") s = el("rect", { x: n.x - n.w / 2, y: n.y - n.h / 2, width: n.w, height: n.h, rx: Math.min(n.w, n.h) * 0.22 }, g);
      else s = el("circle", { cx: n.x, cy: n.y, r: n.r }, g);
      s.setAttribute("class", "tv-shape");
      if (n.title) el("title", null, g).textContent = n.title;
      var lab = null;
      if (n.label) {
        lab = el("text", { x: n.x, y: n.y, class: "tv-label", "font-size": n.fs || (n.shape === "box" ? Math.min(n.h * 0.5, 0.42) : n.r * 0.95) }, g);
        lab.textContent = n.label;
      }
      shapes.set(n.key, { g: g, s: s, lab: lab, n: n });
    });
    var texts = new Map();
    (scene.texts || []).forEach(function (t) {
      var e = el("text", { x: t.x, y: t.y, class: "tv-text " + (t.cls || ""), "text-anchor": t.anchor || "middle", "font-size": t.fs || 0.38 }, gT);
      e.textContent = t.text;
      if (t.key) texts.set(t.key, e);
    });
    return {
      svg: svg, shapes: shapes, texts: texts, unit: u,
      /** stateOf(node) -> 0 | 1 | null ; textOf(key) -> string or undefined */
      update: function (stateOf, textOf) {
        shapes.forEach(function (o) {
          var v = stateOf(o.n);
          o.g.classList.toggle("on", v === 1);
          o.g.classList.toggle("off", v === 0);
        });
        if (textOf) texts.forEach(function (e, k) { var s = textOf(k); if (s !== undefined && e.textContent !== s) e.textContent = s; });
      }
    };
  }

  /** A strip of bits over time: rows = [{label, bits(t)->0|1|null, cls}]. */
  function strips(container, rows, T, opts) {
    opts = opts || {};
    container.innerHTML = "";
    if (!rows.length) return { update: function () {} };
    var cw = opts.cell || Math.max(4, Math.min(16, Math.floor(((container.clientWidth || 700) - 110) / (T + 1))));
    var lh = 15, left = 104, W = left + cw * (T + 1) + 4, H = rows.length * (lh + 3) + 16;
    var svg = el("svg", { width: W, height: H, viewBox: "0 0 " + W + " " + H, class: "tv-strips-svg", role: "img", "aria-label": opts.label || "Histories" }, container);
    rows.forEach(function (row, i) {
      var y = 4 + i * (lh + 3);
      var t = el("text", { x: left - 6, y: y + lh * 0.75, "text-anchor": "end", class: "tv-strip-label" }, svg);
      t.textContent = row.label;
      for (var s = 0; s <= T; s++) {
        var b = row.bits(s);
        if (b === null || b === undefined) continue;
        el("rect", { x: left + s * cw, y: y, width: Math.max(1, cw - 1), height: lh, class: "tv-bit " + (b ? "one " : "zero ") + (row.cls || "") }, svg);
      }
    });
    var axisY = 4 + rows.length * (lh + 3) + 9;
    var step = T <= 40 ? 5 : T <= 120 ? 10 : T <= 400 ? 50 : 100;
    for (var s = 0; s <= T; s += step) {
      var tx = el("text", { x: left + s * cw + cw / 2, y: axisY, "text-anchor": "middle", class: "tv-strip-axis" }, svg);
      tx.textContent = String(s);
    }
    var cursor = el("rect", { x: left, y: 1, width: cw, height: rows.length * (lh + 3) + 2, class: "tv-cursor" }, svg);
    return {
      svg: svg,
      update: function (t) { cursor.setAttribute("x", left + Math.max(0, Math.min(T, t)) * cw - 0.5); }
    };
  }

  scope.TreeDraw = { el: el, render: render, strips: strips };
})(window);
