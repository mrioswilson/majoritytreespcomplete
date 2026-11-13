/* Circuit input formats for the compiler tab: adjacency matrix and gate list.
 * Produces the definition accepted by MajorityEditor.compile:
 *   { inputs: [{id, value}], gates: [{id, op, a, b}], output }
 * Gates with more than two inputs are decomposed into balanced binary trees.
 * No DOM access; usable from the browser and from Node (tests).
 */
(function (scope) {
  "use strict";

  var TYPES = ["IN", "AND", "OR", "NOT", "NAND", "NOR", "XOR", "XNOR"];
  var NAME = /^[A-Za-z][A-Za-z0-9_]{0,19}$/;

  function CircuitInputError(message) { this.name = "CircuitInputError"; this.message = message; }
  CircuitInputError.prototype = Object.create(Error.prototype);
  function fail(message) { throw new CircuitInputError(message); }

  // ------------------------------------------------------------ matrix text
  // Accepts rows separated by newlines (entries separated by spaces, commas or
  // semicolons) or JSON ([[0,1],[0,0]]). Returns an array of rows of 0/1.
  function parseMatrixText(text) {
    var s = String(text || "").trim();
    if (!s) fail("The matrix is empty.");
    var rows;
    if (s.charAt(0) === "[") {
      try { rows = JSON.parse(s); } catch (e) { fail("The matrix is not valid JSON."); }
      if (!Array.isArray(rows) || !rows.every(Array.isArray)) fail("The JSON matrix must be a list of rows.");
    } else {
      rows = s.split(/\r?\n/).map(function (line) { return line.replace(/#.*/, "").trim(); })
        .filter(function (line) { return line.length > 0; })
        .map(function (line) {
          var cells = line.split(/[\s,;]+/).filter(function (c) { return c.length > 0; });
          // Also accept compact rows such as 0101.
          if (cells.length === 1 && /^[01]{2,}$/.test(cells[0])) cells = cells[0].split("");
          return cells;
        });
    }
    var n = rows.length;
    rows = rows.map(function (r, i) {
      if (r.length !== n) fail("The matrix must be square: row " + (i + 1) + " has " + r.length + " entries, expected " + n + ".");
      return r.map(function (v) {
        var x = Number(v);
        if (x !== 0 && x !== 1) fail("Matrix entries must be 0 or 1 (found “" + v + "”).");
        return x;
      });
    });
    return rows;
  }

  // ------------------------------------------------------------ matrix spec
  // spec = { nodes: [{name, type, value}], matrix: [[0/1]], output: name|null }
  // matrix[i][j] = 1 means node i feeds node j.
  function fromMatrix(spec) {
    var nodes = spec.nodes || [], A = spec.matrix || [];
    var n = nodes.length;
    if (n === 0) fail("Add at least one input and one gate.");
    if (A.length !== n || A.some(function (r) { return r.length !== n; })) fail("The matrix size must match the number of nodes (" + n + ").");
    var names = new Set();
    nodes.forEach(function (node, i) {
      var name = String(node.name || "").trim();
      if (!NAME.test(name)) fail("Node " + (i + 1) + ": invalid name “" + name + "” (use a letter followed by letters, digits or _; at most 20 characters).");
      if (names.has(name)) fail("Repeated node name: " + name + ".");
      if (TYPES.indexOf(String(node.type).toUpperCase()) < 0) fail("Node " + name + ": unknown type " + node.type + ".");
      names.add(name);
      if (A[i][i]) fail("Node " + name + " cannot feed itself.");
    });
    var preds = nodes.map(function (_, j) {
      var p = [];
      for (var i = 0; i < n; i++) if (A[i][j]) p.push(i);
      return p;
    });
    var order = topological(n, preds, nodes);
    var inputs = [], gates = [];
    nodes.forEach(function (node, j) {
      var type = String(node.type).toUpperCase();
      if (type === "IN") {
        if (preds[j].length) fail("Input " + node.name + " cannot have incoming edges (column " + (j + 1) + " must be all zeros).");
        inputs.push({ id: node.name, value: node.value ? 1 : 0 });
      }
    });
    if (!inputs.length) fail("The circuit needs at least one input node (type IN).");
    order.forEach(function (j) {
      var node = nodes[j], type = String(node.type).toUpperCase();
      if (type === "IN") return;
      var args = preds[j].map(function (i) { return nodes[i].name; });
      gates.push.apply(gates, expand(node.name, type, args));
    });
    if (!gates.length) fail("The circuit needs at least one gate.");
    var output = spec.output ? String(spec.output) : defaultOutput(nodes, A);
    if (!names.has(output)) fail("The output “" + output + "” is not a node.");
    return { inputs: inputs, gates: gates, output: output };
  }

  function defaultOutput(nodes, A) {
    // The last node without outgoing edges that is a gate.
    for (var j = nodes.length - 1; j >= 0; j--) {
      var sink = A[j].every(function (v) { return !v; });
      if (sink && String(nodes[j].type).toUpperCase() !== "IN") return nodes[j].name;
    }
    return nodes[nodes.length - 1].name;
  }

  function topological(n, preds, nodes) {
    var state = new Array(n).fill(0), order = [];
    function visit(j, path) {
      if (state[j] === 2) return;
      if (state[j] === 1) {
        var cycle = path.slice(path.indexOf(j)).concat([j]).map(function (k) { return nodes[k].name; });
        fail("The circuit has a cycle: " + cycle.join(" → ") + ". Use an acyclic circuit.");
      }
      state[j] = 1;
      path.push(j);
      preds[j].forEach(function (i) { visit(i, path); });
      path.pop();
      state[j] = 2;
      order.push(j);
    }
    for (var j = 0; j < n; j++) visit(j, []);
    return order;
  }

  // Binary decomposition of one node with arguments args.
  function expand(name, type, args) {
    var k = args.length, out = [], counter = 0;
    function helper() {
      counter += 1;
      var id = name + "_" + counter;
      if (!NAME.test(id)) fail("Gate name " + name + " is too long to decompose its inputs; use a shorter name.");
      return id;
    }
    function tree(op, list) { // combines list into one operand with binary op
      while (list.length > 1) {
        var next = [];
        for (var i = 0; i + 1 < list.length; i += 2) {
          var id = helper();
          out.push({ id: id, op: op, a: list[i], b: list[i + 1] });
          next.push(id);
        }
        if (list.length % 2) next.push(list[list.length - 1]);
        list = next;
      }
      return list[0];
    }
    if (type === "NOT") {
      if (k !== 1) fail("NOT gate " + name + " needs exactly one input (it has " + k + ").");
      out.push({ id: name, op: "NOT", a: args[0], b: "" });
      return out;
    }
    if (k < 2) fail(type + " gate " + name + " needs at least two inputs (it has " + k + ").");
    if (type === "AND" || type === "OR") {
      var left = tree(type, args.slice(0, Math.ceil(k / 2)));
      var right = tree(type, args.slice(Math.ceil(k / 2)));
      out.push({ id: name, op: type, a: left, b: right });
    } else if (type === "NAND" || type === "NOR") {
      var base = type === "NAND" ? "AND" : "OR";
      var l2 = tree(base, args.slice(0, Math.ceil(k / 2)));
      var r2 = tree(base, args.slice(Math.ceil(k / 2)));
      out.push({ id: name, op: type, a: l2, b: r2 });
    } else { // XOR, XNOR: parity of all inputs, negated for XNOR
      var l3 = tree("XOR", args.slice(0, Math.ceil(k / 2)));
      var r3 = tree("XOR", args.slice(Math.ceil(k / 2)));
      out.push({ id: name, op: type, a: l3, b: r3 });
    }
    return out;
  }

  // ------------------------------------------------------------ gate list
  //   inputs: a=1, b=0, c
  //   g1 = AND(a, b)
  //   g2 = OR(g1, c, a)
  //   output: g2
  function fromGateList(text) {
    var lines = String(text || "").split(/\r?\n/);
    var inputs = [], gates = [], output = null, names = new Set();
    lines.forEach(function (raw, idx) {
      var line = raw.replace(/#.*/, "").trim();
      if (!line) return;
      var where = " (line " + (idx + 1) + ")";
      var m;
      if ((m = /^inputs?\s*:\s*(.*)$/i.exec(line))) {
        m[1].split(/[\s,;]+/).filter(Boolean).forEach(function (tok) {
          var parts = tok.split("=");
          var id = parts[0].trim(), value = parts.length > 1 ? Number(parts[1]) : 0;
          if (!NAME.test(id)) fail("Invalid input name “" + id + "”" + where + ".");
          if (value !== 0 && value !== 1) fail("Input " + id + " must be 0 or 1" + where + ".");
          if (names.has(id)) fail("Repeated name " + id + where + ".");
          names.add(id);
          inputs.push({ id: id, value: value });
        });
      } else if ((m = /^outputs?\s*:\s*([A-Za-z][A-Za-z0-9_]*)\s*$/i.exec(line))) {
        output = m[1];
      } else if ((m = /^([A-Za-z][A-Za-z0-9_]*)\s*=\s*([A-Za-z]+)\s*\(([^)]*)\)\s*$/.exec(line))) {
        var id = m[1], op = m[2].toUpperCase();
        var args = m[3].split(",").map(function (s) { return s.trim(); }).filter(Boolean);
        if (TYPES.indexOf(op) < 1) fail("Unknown gate type " + m[2] + where + ".");
        if (!NAME.test(id)) fail("Invalid gate name “" + id + "”" + where + ".");
        if (names.has(id)) fail("Repeated name " + id + where + ".");
        names.add(id);
        gates.push({ id: id, op: op, args: args });
      } else {
        fail("Cannot read line " + (idx + 1) + ": “" + line + "”.");
      }
    });
    if (!inputs.length) fail("Declare the inputs, for example “inputs: a=1, b=0”.");
    if (!gates.length) fail("Declare at least one gate, for example “g = AND(a, b)”.");
    // Build the equivalent matrix spec, so both formats share one validator.
    var nodes = inputs.map(function (i) { return { name: i.id, type: "IN", value: i.value }; })
      .concat(gates.map(function (g) { return { name: g.id, type: g.op, value: 0 }; }));
    var index = new Map(nodes.map(function (node, i) { return [node.name, i]; }));
    var n = nodes.length, A = [];
    for (var i = 0; i < n; i++) A.push(new Array(n).fill(0));
    gates.forEach(function (g) {
      var j = index.get(g.id);
      g.args.forEach(function (a) {
        if (!index.has(a)) fail("Gate " + g.id + " uses “" + a + "”, which is not declared.");
        var i = index.get(a);
        if (A[i][j]) fail("Gate " + g.id + " uses " + a + " twice; each input edge can appear once.");
        A[i][j] = 1;
      });
    });
    var spec = { nodes: nodes, matrix: A, output: output };
    return { spec: spec, definition: fromMatrix(spec) };
  }

  // Matrix spec -> gate list text (for the second editor tab).
  function toGateList(spec) {
    var lines = [];
    var ins = spec.nodes.filter(function (n) { return String(n.type).toUpperCase() === "IN"; });
    lines.push("inputs: " + ins.map(function (n) { return n.name + "=" + (n.value ? 1 : 0); }).join(", "));
    spec.nodes.forEach(function (node, j) {
      if (String(node.type).toUpperCase() === "IN") return;
      var args = [];
      spec.nodes.forEach(function (src, i) { if (spec.matrix[i][j]) args.push(src.name); });
      lines.push(node.name + " = " + String(node.type).toUpperCase() + "(" + args.join(", ") + ")");
    });
    lines.push("output: " + (spec.output || defaultOutput(spec.nodes, spec.matrix)));
    return lines.join("\n");
  }

  // Compact, URL-safe encoding of a spec (for shareable links).
  function encodeSpec(spec) {
    var json = JSON.stringify({ n: spec.nodes.map(function (x) { return [x.name, x.type, x.value ? 1 : 0]; }),
      m: spec.matrix.map(function (r) { return r.join(""); }), o: spec.output || null });
    var b64 = typeof btoa === "function" ? btoa(unescape(encodeURIComponent(json)))
      : Buffer.from(json, "utf8").toString("base64");
    return b64.replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  }
  function decodeSpec(code) {
    var b64 = String(code).replace(/-/g, "+").replace(/_/g, "/");
    while (b64.length % 4) b64 += "=";
    var json = typeof atob === "function" ? decodeURIComponent(escape(atob(b64)))
      : Buffer.from(b64, "base64").toString("utf8");
    var o = JSON.parse(json);
    return {
      nodes: o.n.map(function (x) { return { name: x[0], type: x[1], value: x[2] }; }),
      matrix: o.m.map(function (r) { return r.split("").map(Number); }),
      output: o.o
    };
  }

  scope.CircuitInput = {
    TYPES: TYPES, parseMatrixText: parseMatrixText, fromMatrix: fromMatrix,
    fromGateList: fromGateList, toGateList: toGateList,
    encodeSpec: encodeSpec, decodeSpec: decodeSpec, CircuitInputError: CircuitInputError
  };
  if (typeof module !== "undefined" && module.exports) module.exports = scope.CircuitInput;
})(typeof globalThis !== "undefined" ? globalThis : this);
