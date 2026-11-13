/* Majority on trees — "Circuit compiler" tab.
 * Editor adapted from gadgets-site/assets/circuit.js; compiler and simulator:
 * MajorityTree (assets/tree-model.js). The page simulates the macrocell level
 * exactly, with every control following its word.
 */
(function () {
  "use strict";

  var MT = window.MajorityTree, CI = window.CircuitInput, TD = window.TreeDraw;
  var $ = function (s, r) { return (r || document).querySelector(s); };
  var root = $("#circuit");
  if (!root || !MT || !CI || !TD) return;

  // ---------------------------------------------------------------- examples
  function exampleSpec(nodes, edges, output) {
    var names = nodes.map(function (n) { return n[0]; });
    var A = names.map(function () { return names.map(function () { return 0; }); });
    edges.forEach(function (e) { A[names.indexOf(e[0])][names.indexOf(e[1])] = 1; });
    return { nodes: nodes.map(function (n) { return { name: n[0], type: n[1], value: n[2] || 0 }; }), matrix: A, output: output || null };
  }
  var EXAMPLES = {
    and: { label: "AND of two inputs", spec: exampleSpec([["a", "IN", 1], ["b", "IN", 1], ["g", "AND"]], [["a", "g"], ["b", "g"]]) },
    mixed: { label: "(a ∧ b) ∨ c", spec: exampleSpec([["a", "IN", 1], ["b", "IN", 0], ["c", "IN", 1], ["ab", "AND"], ["out", "OR"]],
      [["a", "ab"], ["b", "ab"], ["ab", "out"], ["c", "out"]]) },
    majority: { label: "Majority of three", spec: exampleSpec(
      [["a", "IN", 1], ["b", "IN", 0], ["c", "IN", 1], ["ab", "AND"], ["ac", "AND"], ["bc", "AND"], ["m", "OR"]],
      [["a", "ab"], ["b", "ab"], ["a", "ac"], ["c", "ac"], ["b", "bc"], ["c", "bc"], ["ab", "m"], ["ac", "m"], ["bc", "m"]]) },
    xor: { label: "XOR (negated inputs)", spec: exampleSpec([["a", "IN", 1], ["b", "IN", 0], ["x", "XOR"]], [["a", "x"], ["b", "x"]]) },
    fanout: { label: "Fan-out: (a ∨ b) ∧ (a ∨ c)", spec: exampleSpec([["a", "IN", 0], ["b", "IN", 1], ["c", "IN", 1], ["ab", "OR"], ["ac", "OR"], ["f", "AND"]],
      [["a", "ab"], ["b", "ab"], ["a", "ac"], ["c", "ac"], ["ab", "f"], ["ac", "f"]]) }
  };

  // ---------------------------------------------------------------- state
  var st = { spec: clone(EXAMPLES.mixed.spec), mode: "matrix", def: null, c: null, assignment: {}, t: 0, sel: null, playing: null };
  function clone(o) { return JSON.parse(JSON.stringify(o)); }

  var el = {
    example: $("#cx-example"), modeBtns: root.querySelectorAll("[data-cmode]"), matrixPane: $("#cx-matrix-pane"),
    listPane: $("#cx-list-pane"), nodes: $("#cx-nodes"), matrix: $("#cx-matrix"), output: $("#cx-output"),
    addIn: $("#cx-add-input"), addGate: $("#cx-add-gate"), paste: $("#cx-paste"), pasteApply: $("#cx-paste-apply"),
    list: $("#cx-list"), error: $("#cx-error"), build: $("#cx-build"), ever: $("#cx-ever"), progressLabel: $("#cx-progress-label"),
    results: $("#cx-results"), stats: $("#cx-stats"), assign: $("#cx-assign"), verdict: $("#cx-verdict"),
    checkAll: $("#cx-check-all"), table: $("#cx-truth"), wrap: $("#cx-svg-wrap"), stage: $("#cx-stage"),
    slider: $("#cx-time"), timeLabel: $("#cx-time-label"), play: $("#cx-play"), playSpeed: $("#cx-play-speed"),
    step: $("#cx-step"), stepBack: $("#cx-step-back"), prevIns: $("#cx-prev-ins"), nextIns: $("#cx-next-ins"),
    nextGate: $("#cx-next-gate"), jumpStart: $("#cx-jump-start"), jumpOut: $("#cx-jump-output"), jumpEver: $("#cx-jump-ever"),
    instruction: $("#cx-instruction"), inspect: $("#cx-inspect"), program: $("#cx-program"),
    dlPlan: $("#cx-dl-plan"), dlMacro: $("#cx-dl-macro"), dlSvg: $("#cx-dl-svg"), share: $("#cx-share"),
    fullCard: $("#cx-full"), fullRoot: $("#cx-full-root"), fullExpand: $("#cx-full-expand"), fullCollapse: $("#cx-full-collapse"),
    fullBack: $("#cx-full-back"), fullFwd: $("#cx-full-fwd"), fullTime: $("#cx-full-time"), fullTlabel: $("#cx-full-tlabel"),
    fullInfo: $("#cx-full-info"), fullWrap: $("#cx-full-wrap"), fullStage: $("#cx-full-stage")
  };
  function showError(msg) { el.error.textContent = msg || ""; el.error.hidden = !msg; }

  // ---------------------------------------------------------------- editor
  function renderEditor() {
    var rows = st.spec.nodes.map(function (node, i) {
      var types = CI.TYPES.map(function (t) { return '<option value="' + t + '"' + (t === node.type ? " selected" : "") + ">" + t + "</option>"; }).join("");
      var value = node.type === "IN"
        ? '<label class="cx-val"><input type="checkbox" data-node-value="' + i + '"' + (node.value ? " checked" : "") + "> 1</label>"
        : '<span class="note">—</span>';
      return '<tr><td class="note">' + (i + 1) + "</td>" +
        '<td><input class="cx-name" data-node-name="' + i + '" value="' + escapeAttr(node.name) + '" aria-label="Name of node ' + (i + 1) + '" spellcheck="false"></td>' +
        '<td><select data-node-type="' + i + '" aria-label="Type of node ' + (i + 1) + '">' + types + "</select></td>" +
        "<td>" + value + "</td>" +
        '<td><button type="button" class="cx-del" data-node-del="' + i + '" aria-label="Remove ' + escapeAttr(node.name) + '">✕</button></td></tr>';
    }).join("");
    el.nodes.innerHTML = "<thead><tr><th>#</th><th>Name</th><th>Type</th><th>Test value</th><th></th></tr></thead><tbody>" + rows + "</tbody>";
    var n = st.spec.nodes.length, head = '<th class="corner">from \\ to</th>';
    st.spec.nodes.forEach(function (node) { head += '<th scope="col" title="' + escapeAttr(node.name) + '"><span>' + escapeHtml(node.name) + "</span></th>"; });
    var body = "";
    for (var i = 0; i < n; i++) {
      body += '<tr><th scope="row">' + escapeHtml(st.spec.nodes[i].name) + "</th>";
      for (var j = 0; j < n; j++) {
        var disabled = i === j || st.spec.nodes[j].type === "IN";
        body += '<td><input type="checkbox" data-edge="' + i + "," + j + '"' + (st.spec.matrix[i][j] ? " checked" : "") +
          (disabled ? " disabled" : "") + ' aria-label="' + escapeAttr(st.spec.nodes[i].name + " feeds " + st.spec.nodes[j].name) + '"></td>';
      }
      body += "</tr>";
    }
    el.matrix.innerHTML = "<thead><tr>" + head + "</tr></thead><tbody>" + body + "</tbody>";
    var gates = st.spec.nodes.filter(function (x) { return x.type !== "IN"; });
    if (!st.spec.output || !gates.some(function (g) { return g.name === st.spec.output; })) st.spec.output = gates.length ? defaultOutputName() : null;
    el.output.innerHTML = gates.map(function (g) {
      return '<option value="' + escapeAttr(g.name) + '"' + (g.name === st.spec.output ? " selected" : "") + ">" + escapeHtml(g.name) + "</option>";
    }).join("");
  }
  function defaultOutputName() {
    var nodes = st.spec.nodes, A = st.spec.matrix;
    for (var j = nodes.length - 1; j >= 0; j--) if (nodes[j].type !== "IN" && A[j].every(function (v) { return !v; })) return nodes[j].name;
    var g = nodes.filter(function (x) { return x.type !== "IN"; });
    return g.length ? g[g.length - 1].name : null;
  }
  function addNode(type) {
    var n = st.spec.nodes.length, base = type === "IN" ? "x" : "g", k = 1;
    var taken = new Set(st.spec.nodes.map(function (x) { return x.name; }));
    while (taken.has(base + k)) k++;
    var node = { name: base + k, type: type === "IN" ? "IN" : "AND", value: 0 };
    var at = type === "IN" ? st.spec.nodes.filter(function (x) { return x.type === "IN"; }).length : n;
    st.spec.nodes.splice(at, 0, node);
    st.spec.matrix.forEach(function (row) { row.splice(at, 0, 0); });
    st.spec.matrix.splice(at, 0, new Array(n + 1).fill(0));
    invalidate(); renderEditor();
  }
  function removeNode(i) {
    var name = st.spec.nodes[i].name;
    st.spec.nodes.splice(i, 1);
    st.spec.matrix.splice(i, 1);
    st.spec.matrix.forEach(function (row) { row.splice(i, 1); });
    if (st.spec.output === name) st.spec.output = null;
    invalidate(); renderEditor();
  }
  function onEditorInput(e) {
    var t = e.target, d = t.dataset;
    if (d.nodeName !== undefined) {
      var i = Number(d.nodeName), old = st.spec.nodes[i].name;
      st.spec.nodes[i].name = t.value.trim();
      if (st.spec.output === old) st.spec.output = st.spec.nodes[i].name;
      invalidate();
      if (e.type === "change") renderEditor();
    } else if (d.nodeType !== undefined) {
      var k = Number(d.nodeType);
      st.spec.nodes[k].type = t.value;
      if (t.value === "IN") st.spec.matrix.forEach(function (row) { row[k] = 0; });
      invalidate(); renderEditor();
    } else if (d.nodeValue !== undefined) {
      st.spec.nodes[Number(d.nodeValue)].value = t.checked ? 1 : 0;
      var nm = st.spec.nodes[Number(d.nodeValue)].name;
      st.assignment[nm] = t.checked ? 1 : 0;
      if (st.c) { renderAssign(); runAssignment(); }
    } else if (d.edge !== undefined) {
      var ij = d.edge.split(",").map(Number);
      st.spec.matrix[ij[0]][ij[1]] = t.checked ? 1 : 0;
      invalidate();
      var keep = st.spec.output;
      renderEditor();
      if (keep) { st.spec.output = keep; el.output.value = keep; }
    }
  }
  function applyPaste() {
    try {
      var M = CI.parseMatrixText(el.paste.value), n = M.length;
      if (n !== st.spec.nodes.length) {
        st.spec.nodes = [];
        var gi = 1, xi = 1;
        for (var j = 0; j < n; j++) {
          var incoming = M.some(function (row) { return row[j]; });
          st.spec.nodes.push(incoming ? { name: "g" + (gi++), type: "AND", value: 0 } : { name: "x" + (xi++), type: "IN", value: 0 });
        }
        st.spec.output = null;
      }
      st.spec.matrix = M;
      showError(""); invalidate(); renderEditor();
    } catch (err) { showError(err.message); }
  }
  function setMode(mode) {
    if (mode === st.mode) return;
    if (mode === "list") el.list.value = CI.toGateList(st.spec);
    else {
      try { st.spec = CI.fromGateList(el.list.value).spec; showError(""); } catch (err) { showError(err.message); return; }
      renderEditor();
    }
    st.mode = mode;
    el.modeBtns.forEach(function (b) { b.setAttribute("aria-pressed", String(b.dataset.cmode === mode)); });
    el.matrixPane.hidden = mode !== "matrix";
    el.listPane.hidden = mode !== "list";
  }
  function currentDefinition() {
    if (st.mode === "list") { var parsed = CI.fromGateList(el.list.value); st.spec = parsed.spec; return parsed.definition; }
    return CI.fromMatrix(st.spec);
  }
  function invalidate() {
    stopPlay();
    if (!st.c) return;
    st.c = null; st.def = null;
    el.results.classList.add("stale");
    el.verdict.textContent = "The circuit changed: build the tree again.";
  }

  // ---------------------------------------------------------------- build
  function build() {
    var def;
    try { def = MT.validate(currentDefinition()); } catch (err) { showError(err.message); return; }
    var mc;
    try { mc = MT.toMcvp(def); } catch (err) { showError(err.message); return; }
    if (mc.nodes.length > 40) { showError("This circuit has " + mc.nodes.length + " nodes after lowering; the page is limited to 40."); return; }
    showError("");
    stopPlay();
    var plan = MT.plan(mc, { ever: el.ever.checked });
    st.def = def;
    st.assignment = {};
    def.inputs.forEach(function (i) { st.assignment[i.id] = i.value; });
    st.c = { def: def, mc: mc, plan: plan, size: null, layout: null, run: null, check: null, full: null };
    st.sel = null;
    el.results.hidden = false;
    el.results.classList.remove("stale");
    el.table.innerHTML = "";
    renderAssign();
    runAssignment();
    layoutCells();
    renderProgram();
    st.t = plan.S + 1;
    el.slider.max = String(plan.T + 6);
    setTime(st.t);
    renderStats();
    window.setTimeout(function () { st.c.size = MT.treeSize(plan); renderStats(); }, 30);
  }

  function inputBits() { return MT.inputBits(st.c.mc, st.c.def, st.assignment); }

  function runAssignment() {
    var c = st.c;
    if (!c) return;
    var bits = inputBits();
    c.run = MT.runMacro(c.plan, bits);
    c.check = MT.checkRun(c.plan, bits, c.run);
    c.ix = MT.fullIndex(c.plan, c.run);
    if (!c.full) {
      c.full = { root: c.run.id.g.C, open: new Set() };
      renderFullRoots();
    }
    renderVerdict();
    renderFull();
    setTime(st.t);
  }

  function fmt(n) {
    if (n === null || n === undefined) return "…";
    if (n < 1e6) return n.toLocaleString("en-US");
    var e = Math.floor(Math.log10(n)), m = n / Math.pow(10, e);
    return m.toFixed(2) + " × 10" + String(e).split("").map(function (d) { return "⁰¹²³⁴⁵⁶⁷⁸⁹".charAt(Number(d)); }).join("");
  }
  function renderStats() {
    var c = st.c, p = c.plan, gates = p.nodes.filter(function (n) { return n.kind !== "const"; }).length;
    var items = [
      ["Nodes M", p.M + " (" + gates + " gate" + (gates === 1 ? "" : "s") + ")"], ["Macrocells", (3 * p.M + 5)],
      ["Controls", 6 * (3 * p.M + 5)], ["Program L", p.L + " steps"], ["H", p.H.toLocaleString("en-US")],
      ["S", p.S], ["Output read at T", p.T.toLocaleString("en-US")],
      ["Full tree", c.size ? fmt(c.size.vertices) + " vertices" : "computing…"],
      ["Largest clock", c.size ? fmt(c.size.largestGenerator) + " vertices" : "…"],
      ["Maximum degree", "5 (degrees 1, 3, 5)"], ["Simulated here", c.run ? c.run.graph.st.length + " vertices" : "…"]
    ];
    el.stats.innerHTML = items.map(function (it) { return '<div class="cx-stat"><span>' + escapeHtml(it[0]) + "</span><strong>" + escapeHtml(String(it[1])) + "</strong></div>"; }).join("");
  }
  function renderAssign() {
    el.assign.innerHTML = st.def.inputs.map(function (i) {
      return '<label class="cx-chip"><input type="checkbox" data-assign="' + escapeAttr(i.id) + '"' + (st.assignment[i.id] ? " checked" : "") + "> " + escapeHtml(i.id) + "</label>";
    }).join("");
  }
  function renderVerdict() {
    var c = st.c, k = c.check, p = c.plan;
    var gates = p.checkpoints.length;
    if (k.ok) {
      el.verdict.className = "cx-verdict ok";
      el.verdict.innerHTML = "Output at T = " + p.T.toLocaleString("en-US") + ": <strong>" + k.output + "</strong> (the circuit gives " + k.expected + "). " +
        "Every macrocell is quiescent with the right bits before the program, after each of the " + gates + " gate" + (gates === 1 ? "" : "s") +
        " and at T." + (k.z ? " EVER: z stays 0 until T + 1 and " + (k.z.ever ? "becomes 1 at T + 2." : "never becomes 1.") : "");
    } else {
      el.verdict.className = "cx-verdict bad";
      el.verdict.innerHTML = "Problem: " + escapeHtml(k.problems.join("; ")) + ".";
    }
  }

  // ---------------------------------------------------------------- check all
  var checking = null;
  function checkAll() {
    if (!st.c) return;
    if (checking) { checking.stop = true; checking = null; el.checkAll.textContent = "Check all assignments"; return; }
    var ids = st.def.inputs.map(function (i) { return i.id; });
    if (ids.length > 12) { el.table.innerHTML = "<caption>Too many inputs (" + ids.length + ") to check every assignment here.</caption>"; return; }
    var total = 1 << ids.length, rows = [], job = { stop: false }, k = 0, c = st.c;
    checking = job;
    el.checkAll.textContent = "Stop";
    function next() {
      if (job.stop || st.c !== c) return;
      var t0 = Date.now();
      while (k < total && Date.now() - t0 < 40) {
        var asg = {};
        ids.forEach(function (id, j) { asg[id] = (k >> (ids.length - 1 - j)) & 1; });
        var bits = MT.inputBits(c.mc, c.def, asg), run = MT.runMacro(c.plan, bits), chk = MT.checkRun(c.plan, bits, run);
        rows.push({ asg: asg, chk: chk });
        k++;
      }
      renderTruth(ids, rows, total);
      if (k < total) window.setTimeout(next, 0);
      else { checking = null; el.checkAll.textContent = "Check all assignments"; }
    }
    next();
  }
  function renderTruth(ids, rows, total) {
    var bad = rows.filter(function (r) { return !r.chk.ok; }).length;
    var cap = rows.length < total ? "Checking… " + rows.length + " / " + total :
      (bad ? bad + " of " + total + " assignments failed." : "All " + total + " assignments: every macrocell, the output and EVER are correct.");
    el.table.innerHTML = "<caption>" + cap + "</caption><thead><tr>" + ids.map(function (i) { return "<th>" + escapeHtml(i) + "</th>"; }).join("") +
      "<th>circuit</th><th>tree at T</th>" + (st.c.plan.ever ? "<th>z ever 1</th>" : "") + "<th></th></tr></thead><tbody>" +
      rows.map(function (r) {
        return "<tr>" + ids.map(function (i) { return "<td>" + r.asg[i] + "</td>"; }).join("") + "<td>" + r.chk.expected + "</td><td>" + r.chk.output + "</td>" +
          (st.c.plan.ever ? "<td>" + (r.chk.z && r.chk.z.ever ? 1 : 0) + "</td>" : "") +
          (r.chk.ok ? '<td class="ok">✓</td>' : '<td class="bad">' + escapeHtml(r.chk.problems.slice(0, 2).join("; ")) + "</td>") + "</tr>";
      }).join("") + "</tbody>";
  }

  // ---------------------------------------------------------------- layout
  var DX = 4.2;
  function layoutCells() {
    var p = st.c.plan, M = p.M, pos = {};
    // Each cell: coordinates of A, C, B and of the leaves A', B'; ports go outwards.
    function horiz(name, cx, cy, flip, leafDy) {
      var s = flip ? -1 : 1;
      pos[name] = { A: [cx - s, cy], C: [cx, cy], B: [cx + s, cy], a: [cx - s, cy + leafDy], b: [cx + s, cy + leafDy], free: { A: [-s * 0.8, 0], B: [s * 0.8, 0], C: [0, -leafDy] } };
    }
    function vert(name, cx, cy) {
      pos[name] = { A: [cx, cy], C: [cx, cy + 1], B: [cx, cy + 2], a: [cx + 0.85, cy], b: [cx + 0.85, cy + 2], free: { A: [-0.8, 0], C: [-0.8, 0], B: [0, 0.85] } };
    }
    pos.g = { A: [0.6, -1], C: [0.6, 0], B: [0.6, 1], a: [1.45, -1], b: [1.45, 1], free: {} };
    for (var i = 1; i <= M; i++) {
      horiz("b" + i, i * DX, 0, false, -0.85);
      vert("c" + i, i * DX, 2.1);
      vert("r" + i, i * DX, 5.6);
    }
    horiz("cA", -1.5, -2.5, true, -0.85);
    horiz("rA", -4.5, -2.5, true, -0.85);
    horiz("cB", -1.5, 2.5, true, 0.85);
    horiz("rB", -4.5, 2.5, true, 0.85);
    st.c.layout = pos;
    drawCells();
  }

  function drawCells() {
    var c = st.c, p = c.plan, pos = c.layout, run = c.run, ids = run.id;
    var nodes = [], edges = [], texts = [];
    p.cells.forEach(function (name) {
      var P = pos[name], v = ids[name], sel = st.sel === name ? " selected" : "";
      ["A", "C", "B"].forEach(function (X) {
        nodes.push({ key: name + X, v: v[X], x: P[X][0], y: P[X][1], r: 0.34, cls: "sig cell" + sel, title: name + "." + X, cell: name });
        texts.push({ x: P[X][0] + 0.02, y: P[X][1] - 0.48, text: "", key: "u:" + name + ":" + X, cls: "mode", fs: 0.26 });
      });
      nodes.push({ key: name + "a", v: v.a, x: P.a[0], y: P.a[1], r: 0.2, cls: "sig" + sel, title: name + ".A'", cell: name });
      nodes.push({ key: name + "b", v: v.b, x: P.b[0], y: P.b[1], r: 0.2, cls: "sig" + sel, title: name + ".B'", cell: name });
      edges.push({ a: name + "A", b: name + "C" }, { a: name + "C", b: name + "B" }, { a: name + "A", b: name + "a" }, { a: name + "B", b: name + "b" });
      ["A", "C", "B"].forEach(function (X) {
        if (p.used[name + "." + X]) return;
        var off = P.free[X] || [0, 0.8];
        nodes.push({ key: name + X + "k", x: P[X][0] + off[0], y: P[X][1] + off[1], r: 0.12, cls: "sup cherry", title: "constant-0 cherry", v: null });
        edges.push({ a: name + X, b: name + X + "k" });
      });
      var labelPos = name === "g" ? [-0.35, 0] :
        /^b\d+$/.test(name) ? [P.C[0], P.C[1] - 1.45] :
        /^[cr]\d+$/.test(name) ? [P.A[0] - 1.6, P.C[1]] :
        /A$/.test(name) ? [P.C[0], P.C[1] - 1.5] : [P.C[0], P.C[1] + 1.6];
      texts.push({ x: labelPos[0], y: labelPos[1], text: name, cls: "cell-name", fs: 0.4, anchor: "middle" });
    });
    p.links.forEach(function (l) { edges.push({ a: l.u + l.pu, b: l.v + l.pv, cls: "port-edge" }); });
    if (run.z !== null) {
      var o = pos[p.out].B;
      nodes.push({ key: "z", v: run.z, x: o[0], y: o[1] + 1.15, r: 0.36, cls: "sig port", label: "z", fs: 0.3, title: "EVER receiver z" });
      edges.push({ a: p.out + "B", b: "z", cls: "port-edge" });
      texts.push({ x: o[0] + 0.55, y: o[1] + 1.25, text: "z", anchor: "start", cls: "muted", fs: 0.32 });
    }
    st.c.drawer = TD.render(el.wrap, { nodes: nodes, edges: edges, texts: texts }, {
      maxWidth: Math.max(360, el.stage.clientWidth - 16), unit: 30, minUnit: 14, label: "Macrocells of the compiled tree" });
    renderFrame();
  }

  // ---------------------------------------------------------------- time
  function setTime(t) {
    var c = st.c;
    if (!c) return;
    st.t = Math.max(0, Math.min(c.plan.T + 6, t));
    el.slider.value = String(st.t);
    el.fullTime.max = String(c.plan.T + 6);
    el.fullTime.value = String(st.t);
    renderFrame();
    renderFullFrame();
  }
  function renderFrame() {
    var c = st.c;
    if (!c || !c.drawer || !c.run) return;
    var p = c.plan, t = st.t, res = c.run.res, idx = MT.physIdx(p, t);
    c.drawer.update(function (n) { return n.v === null || n.v === undefined ? null : MT.stateAt(res, n.v, t); }, function (key) {
      if (key.indexOf("u:") !== 0) return undefined;
      var parts = key.split(":"), ci = p.cellIndex[parts[1]], xi = ["A", "C", "B"].indexOf(parts[2]);
      return String(MT.uAt(p, ci, xi, idx));
    });
    el.timeLabel.textContent = "t = " + t.toLocaleString("en-US") + (t === p.T ? " = T" : t < p.S ? " (common delay S = " + p.S + ")" : "");
    var path = instructionPath(idx);
    el.instruction.innerHTML = idx >= 1 && idx <= p.L
      ? "Next transition: program step " + idx + " of " + p.L + " — " + path.map(function (n, i) {
        return (i === path.length - 1 ? "<strong>" : "") + escapeHtml(n.name) + (i === path.length - 1 ? "</strong> (step " + (idx - n.start) + " of " + n.len + ")" : "");
      }).join(" › ")
      : (t <= p.S ? "Before the program: every control plays HOLD during the common delay S." : "After the program: every macrocell holds its bit (HOLD) for ever.");
    renderInspect();
  }
  function instructionPath(idx) {
    var out = [], node = st.c.plan.root;
    while (node.children && node.children.length) {
      var hit = null;
      for (var i = 0; i < node.children.length; i++) {
        var ch = node.children[i];
        if (idx > ch.start && idx <= ch.start + ch.len) { hit = ch; break; }
      }
      if (!hit) break;
      out.push(hit); node = hit;
    }
    return out;
  }
  function leafStarts() {
    var c = st.c;
    if (c.leafStarts) return c.leafStarts;
    var s = [];
    (function walk(n) { if (!n.children || !n.children.length) { s.push(n.start); return; } n.children.forEach(walk); })(c.plan.root);
    c.leafStarts = s.filter(function (x, i) { return i === 0 || x !== s[i - 1]; });
    return c.leafStarts;
  }
  function jumpIns(dir) {
    var p = st.c.plan, idx = MT.physIdx(p, st.t), starts = leafStarts();
    // A primitive starting at step index s (0-based) begins at physical time S + s + 1.
    var target = null;
    if (dir > 0) { for (var i = 0; i < starts.length; i++) if (p.S + starts[i] + 1 > st.t) { target = p.S + starts[i] + 1; break; } }
    else { for (var j = starts.length - 1; j >= 0; j--) if (p.S + starts[j] + 1 < st.t) { target = p.S + starts[j] + 1; break; } }
    stopPlay();
    setTime(target === null ? (dir > 0 ? p.S + p.L + 1 : p.S + 1) : target);
  }
  function jumpGate() {
    var p = st.c.plan, gates = p.root.children, target = p.S + p.L + 1;
    for (var i = 0; i < gates.length; i++) if (p.S + gates[i].start + 1 > st.t) { target = p.S + gates[i].start + 1; break; }
    stopPlay(); setTime(target);
  }
  function togglePlay() {
    if (st.playing) { stopPlay(); return; }
    if (!st.c) return;
    el.play.textContent = "Pause";
    st.playing = window.setInterval(function () {
      var p = st.c.plan, n = Number(el.playSpeed.value) || 1;
      if (st.t >= p.T + 6) { stopPlay(); return; }
      setTime(st.t + n);
    }, 110);
  }
  function stopPlay() {
    if (st.playing) { window.clearInterval(st.playing); st.playing = null; }
    if (el.play) el.play.textContent = "Play";
  }

  // ---------------------------------------------------------------- program and inspector
  function renderProgram() {
    var p = st.c.plan, rows = p.root.children.map(function (g) {
      var a = p.S + g.start + 1, b = p.S + g.start + g.len + 1;
      return '<li><button type="button" class="ghost-btn cx-gate-btn" data-jump="' + a + '">' + escapeHtml(g.name) + "</button> " +
        '<span class="note">t = ' + a.toLocaleString("en-US") + " … " + b.toLocaleString("en-US") + " · " + g.children.map(function (x) { return escapeHtml(x.name); }).join(", ") + "</span></li>";
    });
    el.program.innerHTML = rows.length ? "<ol>" + rows.join("") + "</ol>" : '<p class="note">The circuit has no gates: the output is an input register.</p>';
  }
  function renderInspect() {
    var c = st.c, name = st.sel;
    if (!name) { el.inspect.innerHTML = '<p class="note">Select a macrocell in the view to see its six control words.</p>'; return; }
    var p = c.plan, ci = p.cellIndex[name], t = st.t, idx = MT.physIdx(p, t), MODE = ["AND", "MAJ", "OR"];
    var v = c.run.id[name], bits = [v.A, v.C, v.B, v.a, v.b].map(function (x) { return MT.stateAt(c.run.res, x, t); });
    var html = "<h4>Macrocell " + escapeHtml(name) + "</h4><p class=\"note\">A C B A' B' at t = " + t + ": " + bits.join(" ") +
      ". Controls in 1: " + ["A", "C", "B"].map(function (X, xi) { var u = MT.uAt(p, ci, xi, idx); return X + " " + u + " (" + MODE[u] + ")"; }).join(", ") + ".</p>";
    html += '<div class="cx-scroll"><table class="readout"><thead><tr><th>control</th><th>changes K</th><th>generator</th><th>word around t</th><th></th></tr></thead><tbody>';
    ["A", "C", "B"].forEach(function (X, xi) {
      for (var j = 1; j <= 2; j++) {
        var h = MT.controlHist(p, ci, xi, j), size = MT.generatorSize(h), strip = "";
        for (var s = t - 12; s <= t + 12; s++) {
          var b = s < 0 ? null : h.at(s);
          strip += b === null ? '<span class="mini none"></span>' : '<span class="mini ' + (b ? "one" : "zero") + (s === t ? " now" : "") + '"></span>';
        }
        html += "<tr><td>" + X + j + "</td><td>" + h.K() + "</td><td>" + fmt(size) + " vertices</td><td class=\"mini-strip\">" + strip +
          '</td><td><button type="button" class="ghost-btn cx-unfold" data-unfold="' + escapeAttr(name + "|" + xi + "|" + j) + '">Unfold</button></td></tr>';
      }
    });
    html += "</tbody></table></div>";
    el.inspect.innerHTML = html;
  }

  // ---------------------------------------------------------------- full tree
  var SUP = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" };
  function fmtShort(n) {
    if (n < 10000) return n.toLocaleString("en-US");
    var e = Math.floor(Math.log10(n));
    return (n / Math.pow(10, e)).toFixed(1) + "·10" + String(e).split("").map(function (d) { return SUP[d]; }).join("");
  }
  function renderFullRoots() {
    var c = st.c, opts = [];
    c.plan.cells.forEach(function (name) {
      ["A", "C", "B"].forEach(function (X) { opts.push([c.run.id[name][X], name + "." + X]); });
    });
    if (c.run.z !== null) opts.push([c.run.z, "z (receiver)"]);
    el.fullRoot.innerHTML = opts.map(function (o) {
      return '<option value="' + o[0] + '"' + (o[0] === c.full.root ? " selected" : "") + ">" + escapeHtml(o[1]) + "</option>";
    }).join("");
    var small = c.ix.total <= 6000;
    el.fullExpand.disabled = !small;
    el.fullExpand.title = small ? "" : "The full tree has " + fmt(c.ix.total) + " vertices: unfold it part by part.";
  }
  function vertexLabel(n) {
    if (n.type === "macro") return n.label;
    if (n.s.kind === "node") return "node K=" + n.s.h.K();
    return /^(pulse|timer)$/.test(n.s.kind) ? n.label : "";
  }
  function boxLabel(n) {
    if (n.type === "macro") return n.label || "subtree";
    var s = n.s;
    if (s.kind === "node") return "node K=" + s.h.K();
    if (s.kind === "cherry") return "const " + s.b;
    if (s.kind === "arm") return "arm v" + s.i + "…";
    return n.label;
  }
  function fullTooltip(n) {
    if (n.type === "macro") return (n.label || "vertex") + (n.box ? ": " + n.size.toLocaleString("en-US") + " vertices behind this edge" : "");
    return (n.what ? n.what + ": " : "") + n.label + " (" + n.size.toLocaleString("en-US") + " vertices)";
  }
  /** Compact layered layout (contours, as in Reingold-Tilford): siblings are
   * packed as close as their subtrees allow; a vertex sits above the middle of
   * its children, or above a child that is much deeper than the others, so
   * long chains (timer arms) go straight down. Sets n.x and n.y (depth). */
  function tidy(root, widthOf, gap) {
    function walk(n) {
      var ext = widthOf(n), wl = ext[0], wr = ext[1];
      if (!n.children.length) { n._off = []; return { l: [-wl], r: [wr] }; }
      var cs = n.children.map(walk), offs = [0], L = cs[0].l.slice(), R = cs[0].r.slice(), d;
      for (var i = 1; i < cs.length; i++) {
        var c = cs[i], shift = -Infinity;
        for (d = 0; d < Math.min(R.length, c.l.length); d++) shift = Math.max(shift, R[d] + gap - c.l[d]);
        offs.push(shift);
        for (d = 0; d < c.l.length; d++) {
          if (d < R.length) R[d] = Math.max(R[d], c.r[d] + shift);
          else { L.push(c.l[d] + shift); R.push(c.r[d] + shift); }
        }
      }
      var px = (offs[0] + offs[offs.length - 1]) / 2;
      var depths = cs.map(function (c) { return c.l.length; }), maxD = Math.max.apply(null, depths), deep = depths.indexOf(maxD);
      var others = depths.filter(function (x, k) { return k !== deep; });
      if (others.length && maxD >= 4 && Math.max.apply(null, others) <= 2) px = offs[deep];
      n._off = offs.map(function (o) { return o - px; });
      var l = [-wl], r = [wr];
      for (d = 0; d < L.length; d++) { l.push(L[d] - px); r.push(R[d] - px); }
      return { l: l, r: r };
    }
    walk(root);
    (function place(n, x, depth) {
      n.x = x; n.y = depth;
      n.children.forEach(function (c, i) { place(c, x + n._off[i], depth + 1); });
    })(root, 0, 0);
  }
  function centerOn(key) {
    var g = el.fullWrap.querySelector('[data-key="' + key + '"]');
    if (!g) return;
    var r = g.getBoundingClientRect(), s = el.fullStage.getBoundingClientRect();
    el.fullStage.scrollLeft += (r.left + r.width / 2) - (s.left + s.width / 2);
    el.fullStage.scrollTop += (r.top + r.height / 2) - (s.top + s.height / 3);
  }
  function renderFull(focus) {
    var c = st.c;
    if (!c || !c.ix) return;
    var F = c.full, view = MT.explore(c.ix, F.root, F.open, 4000);
    var exr = MT.exploreRun(c.ix, view, c.plan.T + 6);
    var nodes = [], edges = [], texts = [], DY = 1.7, byKey = {};
    tidy(view.tree, function (n) {
      if (n.box) return [1.65, 1.65];
      var lab = vertexLabel(n);
      return [0.5, 0.5 + (lab ? 0.18 * lab.length + 0.15 : 0)];
    }, 0.3);
    (function scale(n) { n.y *= DY; n.children.forEach(scale); })(view.tree);
    var shown = 0, boxes = 0;
    (function draw(n, parent) {
      byKey[n.key] = n;
      var support = n.type === "sub" && (n.s.kind === "cherry" || n.s.kind === "leaf");
      var cls = support ? "sup" : "sig";
      if (n.box) {
        boxes++;
        nodes.push({ key: n.key, node: n, x: n.x, y: n.y, shape: "box", w: 3.15, h: 0.74, cls: cls + " fold",
          label: boxLabel(n) + " · " + fmtShort(n.size), fs: 0.3, title: fullTooltip(n) });
      } else {
        shown++;
        var leaf = !n.children.length;
        var r = n.type === "sub" && n.s.kind === "leaf" ? 0.17 : leaf ? 0.22 : 0.3;
        nodes.push({ key: n.key, node: n, x: n.x, y: n.y, r: r, cls: cls + (n === view.tree ? " port" : n.open ? " unfolded" : ""), title: fullTooltip(n) });
        var lab = vertexLabel(n);
        if (lab) texts.push({ x: n.x + r + 0.1, y: n.y - 0.02, text: lab, anchor: "start", cls: "muted", fs: 0.3 });
      }
      if (parent) edges.push({ a: parent.key, b: n.key });
      n.children.forEach(function (ch) { draw(ch, n); });
    })(view.tree, null);
    c.fullView = view; c.fullRun = exr; c.fullByKey = byKey;
    c.fullDrawer = TD.render(el.fullWrap, { nodes: nodes, edges: edges, texts: texts }, {
      maxWidth: Math.max(360, el.fullStage.clientWidth - 16), unit: 34, minUnit: 30, label: "Full tree" });
    el.fullInfo.innerHTML = "Showing " + shown.toLocaleString("en-US") + " vertices and " + boxes.toLocaleString("en-US") +
      " folded subtrees of the full tree (" + fmt(c.ix.total) + " vertices)." +
      (exr.simulated ? " The " + exr.simulated.toLocaleString("en-US") + " unfolded clock vertices were simulated with the majority rule" +
        (exr.mismatches ? ', and <strong class="bad">' + exr.mismatches + " differ from their proven histories</strong>." : " and follow their proven histories at every step.") : "") +
      (view.truncated ? " Only the first 4,000 vertices are drawn." : "");
    renderFullFrame();
    var key = focus || view.tree.key;
    window.requestAnimationFrame(function () { centerOn(key); });
  }
  function renderFullFrame() {
    var c = st.c;
    if (!c || !c.fullDrawer) return;
    var t = st.t;
    c.fullDrawer.update(function (sn) {
      var n = sn.node;
      if (!n) return null;
      if (n.type === "macro") return MT.stateAt(c.run.res, n.v, t);
      if (n.box) return MT.subValue(n.s, t);
      var x = c.fullRun.gid[n.key];
      return x === undefined ? null : MT.stateAt(c.fullRun.res, x, t);
    });
    el.fullTlabel.textContent = "t = " + t.toLocaleString("en-US") + (t === c.plan.T ? " = T" : "");
  }
  function onFullClick(e) {
    var g = e.target.closest(".tv-node");
    if (!g || !st.c || !st.c.fullByKey) return;
    var n = st.c.fullByKey[g.getAttribute("data-key")], F = st.c.full;
    if (!n) return;
    if (n.box) F.open.add(n.key);
    else if (n.open && n !== st.c.fullView.tree) { F.open.delete(n.key); if (F.open.all) { F.open = new Set(); } }
    else return;
    renderFull(n.key);
  }
  function unfoldControl(spec) {
    var parts = spec.split("|"), name = parts[0], xi = Number(parts[1]), j = Number(parts[2]), c = st.c;
    var X = ["A", "C", "B"][xi], v = c.run.id[name][X], ctrl = c.run.id[name].ctrl[xi * 2 + j - 1];
    c.full.root = v;
    c.full.open = new Set(["m" + v + "/s" + ctrl]);
    renderFullRoots();
    renderFull("m" + v + "/s" + ctrl);
    el.fullCard.scrollIntoView({ behavior: "smooth", block: "start" });
  }

  // ---------------------------------------------------------------- downloads
  function planExport() {
    var c = st.c, p = c.plan, controls = [];
    p.cells.forEach(function (name, ci) {
      ["A", "C", "B"].forEach(function (X, xi) {
        for (var j = 1; j <= 2; j++) { var h = MT.controlHist(p, ci, xi, j); controls.push({ cell: name, vertex: X, control: j, initial: h.b0, changes: h.ch }); }
      });
    });
    var bits = inputBits();
    return {
      format: "majority-trees-plan/1", rule: "synchronous majority of neighbours, ties keep the state",
      circuit: { nodes: p.nodes, names: p.names, inputBits: bits }, M: p.M, L: p.L, H: p.H, S: p.S, T: p.T, ever: p.ever,
      cells: p.cells.map(function (name) {
        var reg = /^r(\d+)$/.exec(name);
        return { name: name, initial: reg && bits[Number(reg[1]) - 1] !== null ? bits[Number(reg[1]) - 1] : 0 };
      }),
      ports: p.links.map(function (l) { return { from: l.u + "." + l.pu, to: l.v + "." + l.pv }; }),
      constantPorts: p.cells.reduce(function (acc, name) { ["A", "C", "B"].forEach(function (X) { if (!p.used[name + "." + X]) acc.push(name + "." + X); }); return acc; }, []),
      receiver: p.ever ? { attachedTo: p.out + ".B", timerDate: p.T + 1 } : null,
      controls: controls,
      note: "Each macrocell is a path A - C - B with leaves A', B'; every main vertex has its port, two controls and two memory neighbours. " +
        "Control j of a vertex plays [j <= u(t)]; its port follows the history (initial, changes) with the common delay S already included. " +
        "tools/expand_tree.py builds the full tree from this file."
    };
  }
  function saveFile(name, parts, type) {
    var a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob(parts, { type: type }));
    a.download = name;
    document.body.appendChild(a); a.click();
    window.setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  }
  function dlPlan() { if (st.c) saveFile("majority-tree-plan.json", [JSON.stringify(planExport())], "application/json"); }
  function dlMacro() {
    if (!st.c) return;
    var g = st.c.run.graph, verts = g.st.map(function (s, i) { return { id: i, state: s, role: g.role[i] || "" }; }), edges = [];
    for (var k = 0; k < g.au.length; k += 2) edges.push(g.aw[k] > 1 ? [g.au[k], g.av[k], g.aw[k]] : [g.au[k], g.av[k]]);
    var p = st.c.plan, forced = g.forced.map(function (f) {
      var ch = [], prev = f.seq(0);
      MT.controlEvents(p).forEach(function (t) { var b = f.seq(t); if (b !== prev) { ch.push(t); prev = b; } });
      return { vertex: f.v, initial: f.seq(0), changes: ch };
    });
    saveFile("majority-tree-macrocells.json", [JSON.stringify({
      format: "majority-trees-macro/1", rule: "synchronous majority of neighbours, ties keep the state", steps: p.T + 6,
      vertices: verts, edges: edges, forced: forced,
      note: "Forced vertices are the controls (and the timer of z): each follows its history instead of the rule; in the full tree it is the port of a generator. An edge [u, v, k] means that u counts v k times (k identical leaves)."
    })], "application/json");
  }
  function dlSvg() {
    if (!st.c || !st.c.drawer) return;
    var svg = st.c.drawer.svg.cloneNode(true);
    svg.setAttribute("xmlns", "http://www.w3.org/2000/svg");
    var css = "line{stroke:#9aa7b5;stroke-width:.06}.port-edge line,line.port-edge{stroke:#424e5d;stroke-width:.09}circle,rect{stroke:#424e5d;stroke-width:.05;fill:#fff}" +
      ".on.sig circle,.on.sig rect{fill:#0088a5}.on.sup circle{fill:#424e5d}text{font-family:sans-serif;fill:#17202a;text-anchor:middle;dominant-baseline:central}";
    var style = document.createElementNS("http://www.w3.org/2000/svg", "style");
    style.textContent = css;
    svg.insertBefore(style, svg.firstChild);
    saveFile("majority-tree-t" + st.t + ".svg", [new XMLSerializer().serializeToString(svg)], "image/svg+xml");
  }

  // ---------------------------------------------------------------- share and tabs
  function shareLink() {
    var spec;
    try { if (st.mode === "list") spec = CI.fromGateList(el.list.value).spec; else spec = st.spec; } catch (err) { showError(err.message); return; }
    var code = CI.encodeSpec(spec), url = window.location.href.split("#")[0].split("?")[0] + "#circuit=" + code;
    try { window.history.replaceState(null, "", "#circuit=" + code); } catch (e) { /* ignore */ }
    el.share.value = url; el.share.hidden = false; el.share.select();
  }
  function showTab(name, pushHash) {
    document.body.dataset.tab = name;
    document.querySelectorAll("[data-tab-btn]").forEach(function (b) { b.setAttribute("aria-selected", String(b.dataset.tabBtn === name)); });
    $("#explorer").hidden = name !== "gadgets";
    root.hidden = name !== "circuit";
    if (pushHash) { try { window.history.replaceState(null, "", name === "circuit" ? "#circuit" : "#"); } catch (e) { /* ignore */ } }
    if (name === "circuit" && st.c) { drawCells(); renderFull(); }
    window.dispatchEvent(new Event("resize"));
  }
  function fromHash() {
    var h = window.location.hash;
    if (h.indexOf("#circuit") !== 0) return false;
    var m = /^#circuit=([A-Za-z0-9_-]+)$/.exec(h);
    if (m) { try { st.spec = CI.decodeSpec(m[1]); } catch (e) { showError("The shared circuit link could not be read."); } }
    return true;
  }

  function escapeHtml(s) { return String(s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); }
  var escapeAttr = escapeHtml;

  // ---------------------------------------------------------------- boot
  function init() {
    el.example.innerHTML = '<option value="">Load an example…</option>' + Object.keys(EXAMPLES).map(function (k) {
      return '<option value="' + k + '">' + escapeHtml(EXAMPLES[k].label) + "</option>";
    }).join("");
    el.example.addEventListener("change", function () {
      var ex = EXAMPLES[el.example.value];
      if (!ex) return;
      st.spec = clone(ex.spec);
      if (st.mode === "list") el.list.value = CI.toGateList(st.spec);
      showError(""); invalidate(); renderEditor();
      el.example.value = "";
    });
    el.modeBtns.forEach(function (b) { b.addEventListener("click", function () { setMode(b.dataset.cmode); }); });
    root.addEventListener("input", function (e) { if (e.target.closest("#cx-matrix-pane")) onEditorInput(e); });
    root.addEventListener("change", function (e) {
      if (e.target.closest("#cx-matrix-pane")) onEditorInput(e);
      if (e.target.dataset && e.target.dataset.assign !== undefined) { st.assignment[e.target.dataset.assign] = e.target.checked ? 1 : 0; runAssignment(); }
    });
    el.output.addEventListener("change", function () { st.spec.output = el.output.value; invalidate(); });
    el.nodes.addEventListener("click", function (e) { var b = e.target.closest("[data-node-del]"); if (b) removeNode(Number(b.dataset.nodeDel)); });
    el.addIn.addEventListener("click", function () { addNode("IN"); });
    el.addGate.addEventListener("click", function () { addNode("GATE"); });
    el.pasteApply.addEventListener("click", applyPaste);
    el.list.addEventListener("input", invalidate);
    el.ever.addEventListener("change", invalidate);
    el.build.addEventListener("click", build);
    el.checkAll.addEventListener("click", checkAll);
    el.slider.addEventListener("input", function () { stopPlay(); setTime(Number(el.slider.value)); });
    el.play.addEventListener("click", togglePlay);
    el.step.addEventListener("click", function () { stopPlay(); setTime(st.t + 1); });
    el.stepBack.addEventListener("click", function () { stopPlay(); setTime(st.t - 1); });
    el.prevIns.addEventListener("click", function () { if (st.c) jumpIns(-1); });
    el.nextIns.addEventListener("click", function () { if (st.c) jumpIns(1); });
    el.nextGate.addEventListener("click", function () { if (st.c) jumpGate(); });
    el.jumpStart.addEventListener("click", function () { if (st.c) { stopPlay(); setTime(st.c.plan.S + 1); } });
    el.jumpOut.addEventListener("click", function () { if (st.c) { stopPlay(); setTime(st.c.plan.T); } });
    el.jumpEver.addEventListener("click", function () { if (st.c) { stopPlay(); setTime(st.c.plan.T + 2); } });
    el.program.addEventListener("click", function (e) { var b = e.target.closest("[data-jump]"); if (b) { stopPlay(); setTime(Number(b.dataset.jump)); } });
    el.wrap.addEventListener("click", function (e) {
      var g = e.target.closest(".tv-node");
      if (!g || !st.c) return;
      var key = g.getAttribute("data-key"), name = null;
      st.c.plan.cells.forEach(function (n) { if (key.indexOf(n) === 0 && /^[ACBab]k?$/.test(key.slice(n.length))) name = n; });
      if (name) { st.sel = st.sel === name ? null : name; drawCells(); }
    });
    el.fullWrap.addEventListener("click", onFullClick);
    el.fullRoot.addEventListener("change", function () { if (!st.c) return; st.c.full.root = Number(el.fullRoot.value); st.c.full.open = new Set(); renderFull(); });
    el.fullExpand.addEventListener("click", function () { if (!st.c) return; var o = new Set(); o.all = true; st.c.full.open = o; renderFull(); });
    el.fullCollapse.addEventListener("click", function () { if (!st.c) return; st.c.full.open = new Set(); renderFull(); });
    el.fullBack.addEventListener("click", function () { stopPlay(); setTime(st.t - 1); });
    el.fullFwd.addEventListener("click", function () { stopPlay(); setTime(st.t + 1); });
    el.fullTime.addEventListener("input", function () { stopPlay(); setTime(Number(el.fullTime.value)); });
    el.inspect.addEventListener("click", function (e) { var b = e.target.closest("[data-unfold]"); if (b && st.c) unfoldControl(b.dataset.unfold); });
    el.dlPlan.addEventListener("click", dlPlan);
    el.dlMacro.addEventListener("click", dlMacro);
    el.dlSvg.addEventListener("click", dlSvg);
    $("#cx-share-btn").addEventListener("click", shareLink);
    document.querySelectorAll("[data-tab-btn]").forEach(function (b) { b.addEventListener("click", function () { showTab(b.dataset.tabBtn, true); }); });
    document.querySelectorAll("[data-tab-link]").forEach(function (a) {
      a.addEventListener("click", function (e) { e.preventDefault(); showTab(a.dataset.tabLink, true); $(".view-tabs").scrollIntoView({ behavior: "smooth" }); });
    });
    var resizeTimer = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(function () { if (st.c && !root.hidden) { drawCells(); renderFull(); } }, 120);
    });
    window.addEventListener("hashchange", function () {
      if (fromHash()) { renderEditor(); showTab("circuit", false); }
      else if ((window.location.hash || "").indexOf("#gadget") === 0 || !window.location.hash) showTab("gadgets", false);
    });
    var onCircuit = fromHash();
    renderEditor();
    if (!document.body.classList.contains("embed")) showTab(onCircuit ? "circuit" : "gadgets", false);
  }

  // Read-only hook used by the automated tests.
  window.MajorityTreeCompiler = { state: st, build: build, setTime: setTime, planExport: planExport, checkAll: checkAll };
  init();
})();
