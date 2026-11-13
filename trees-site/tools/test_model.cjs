#!/usr/bin/env node
/* Compares the page's model (assets/tree-model.js) with the verified Python
 * implementation of the degree-5 construction, through tools/reference.json
 * (written by tools/make_reference.py). Checks, for words, the structure and
 * size of every generator and the port of the JS tree against an adversarial
 * consumer; for circuits, the plan (L, H, S, T, checkpoints, every control
 * history), the size of the full tree, and the exact history of every
 * macrocell vertex for every input assignment.
 *
 *   node tools/test_model.cjs
 */
"use strict";
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const MT = require(path.join(__dirname, "..", "assets", "tree-model.js"));

const ref = JSON.parse(fs.readFileSync(path.join(__dirname, "reference.json"), "utf8"));
let failures = 0, checks = 0;
function fail(msg) { failures++; if (failures <= 20) console.log("FAIL", msg); }
const sha = (s) => crypto.createHash("sha256").update(s).digest("hex");

function fingerprint(h) {
  const K = h.K();
  if (K === 0) return "C" + h.b0;
  if (K === 1) return (h.b0 === 0 ? "U" : "D") + h.ch[0];
  if (K === 2) return (h.b0 === 1 ? "~" : "") + "P[" + h.ch[0] + "," + h.ch[1] + ")";
  return "N(" + [0, 1, 2, 3].map((j) => fingerprint(h.child(j))).join(",") + ")";
}

// ---------------------------------------------------------------- words
let simulated = 0;
ref.words.forEach((r) => {
  const w = r.w.split("").map(Number), h = MT.wordHist(w);
  checks++;
  if (fingerprint(h) !== r.fp) fail("word " + r.w + ": structure " + fingerprint(h) + " vs " + r.fp);
  if (MT.generatorSize(h) !== r.size) fail("word " + r.w + ": size " + MT.generatorSize(h) + " vs " + r.size);
  if (w.length <= 9 || w.length === 17) {
    const g = new MT.Graph(w.length <= 9), G = MT.generator(g, h), T = MT.S_of(w.length - 1) + w.length + 3;
    const exp = []; for (let t = 0; t <= T; t++) exp.push(MT.wordValue(w, t));
    const e = g.add(0); g.link(G.port, e); g.force(e, MT.consumer("anti", exp));
    const res = MT.simulate(g, T, { frames: true });
    for (let t = 0; t <= T; t++) if (res.frames[t][G.port] !== exp[t]) { fail("word " + r.w + ": port differs at t = " + t); break; }
    if (!g.compress && g.st.length - 1 !== G.size) fail("word " + r.w + ": explicit vertex count " + (g.st.length - 1) + " vs " + G.size);
    simulated++;
  }
});

// ---------------------------------------------------------------- circuits
let runs = 0;
ref.circuits.forEach((c) => {
  const nodes = c.nodes.map((n) => (n[0] === "IN" ? { kind: "const" } : { kind: n[0].toLowerCase(), p: n[1], q: n[2] }));
  const p = MT.plan({ nodes: nodes }, { ever: c.ever });
  const tag = JSON.stringify(c.nodes) + (c.ever ? " EVER" : "");
  checks++;
  ["L", "H", "S", "T"].forEach((k) => { if (p[k] !== c[k]) fail(tag + ": " + k + " " + p[k] + " vs " + c[k]); });
  if (JSON.stringify(p.checkpoints) !== JSON.stringify(c.checkpoints)) fail(tag + ": checkpoints");
  const controls = [];
  p.cells.forEach((name, ci) => { for (let xi = 0; xi < 3; xi++) for (let j = 1; j <= 2; j++) { const h = MT.controlHist(p, ci, xi, j); controls.push([h.b0].concat(h.ch)); } });
  if (sha(JSON.stringify(controls)) !== c.controls) fail(tag + ": control histories");
  const size = MT.treeSize(p).vertices;
  if (size !== c.size) fail(tag + ": tree size " + size + " vs " + c.size);
  c.macro.forEach((m) => {
    let k = 0;
    const bits = nodes.map((n) => (n.kind === "const" ? m.bits[k++] : null));
    const run = MT.runMacro(p, bits), Tmax = p.T + 6;
    const d = crypto.createHash("sha256");
    p.cells.forEach((name) => {
      const v = run.id[name];
      [v.A, v.C, v.B, v.a, v.b].forEach((x) => {
        const buf = Buffer.alloc(Tmax + 1);
        for (let t = 0; t <= Tmax; t++) buf[t] = MT.stateAt(run.res, x, t);
        d.update(buf);
      });
    });
    if (d.digest("hex") !== m.cells) fail(tag + " bits " + m.bits.join("") + ": macrocell histories differ from the Python run");
    const chk = MT.checkRun(p, bits, run);
    if (!chk.ok) fail(tag + " bits " + m.bits.join("") + ": " + chk.problems.join("; "));
    runs++;
  });
});

console.log(JSON.stringify({ words: ref.words.length, wordsSimulated: simulated, circuitPlans: ref.circuits.length, macroRuns: runs, checks: checks, failures: failures }));
console.log(failures ? "MODEL TEST FAILED" : "MODEL TEST PASSED");
process.exitCode = failures ? 1 : 0;
