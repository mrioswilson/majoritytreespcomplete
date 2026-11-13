#!/usr/bin/env node
/* Tests of the full-tree explorer of the compiler (assets/tree-model.js):
 *  - the index counts exactly the vertices of the full tree (treeSize);
 *  - in every view, shown vertices plus the sizes of the folded boxes add up
 *    to the whole tree;
 *  - every unfolded clock vertex, simulated with the majority rule, follows
 *    its proven history at every step;
 *  - unfolding more does not change the states of what was already shown;
 *  - a small tree unfolds completely.
 *
 *   node tools/test_explorer.cjs
 */
"use strict";
const path = require("path");
const MT = require(path.join(__dirname, "..", "assets", "tree-model.js"));

let failures = 0, views = 0, simulated = 0;
function fail(msg) { failures++; if (failures <= 20) console.log("FAIL", msg); }
const rnd = MT.mulberry32(20261007);

function circuit(nodes) { return { nodes: nodes.map((n) => (n[0] === "IN" ? { kind: "const" } : { kind: n[0], p: n[1], q: n[2] })) }; }
const CIRCUITS = [
  [["IN"]],
  [["IN"], ["and", 1, 1]],
  [["IN"], ["IN"], ["or", 1, 2]],
  [["IN"], ["IN"], ["and", 2, 1]],
  [["IN"], ["IN"], ["IN"], ["and", 1, 2], ["or", 4, 3]]
];

function check(view, ix, tag) {
  let shown = 0, boxed = 0;
  (function walk(n) { if (n.box) boxed += n.size; else shown++; n.children.forEach(walk); })(view.tree);
  if (!view.truncated && shown + boxed !== ix.total) fail(tag + ": shown " + shown + " + folded " + boxed + " != total " + ix.total);
  const exr = MT.exploreRun(ix, view, ix.p.T + 6);
  if (exr.mismatches) fail(tag + ": " + exr.mismatches + " unfolded clock vertices differ from their proven histories");
  views++; simulated += exr.simulated;
  return exr;
}
function keysOf(view) {
  const out = [];
  (function walk(n) { if (n.box) out.push(n.key); n.children.forEach(walk); })(view.tree);
  return out;
}
function history(exr, key, T) {
  const x = exr.gid[key];
  if (x === undefined) return null;
  let s = "";
  for (let t = 0; t <= T; t++) s += MT.stateAt(exr.res, x, t);
  return s;
}

CIRCUITS.forEach((nodes) => {
  [false, true].forEach((ever) => {
    const mc = circuit(nodes), p = MT.plan(mc, { ever: ever }), M = nodes.length;
    const inputs = nodes.filter((n) => n[0] === "IN").length;
    for (let a = 0; a < (1 << inputs); a++) {
      let k = 0;
      const bits = mc.nodes.map((n) => (n.kind === "const" ? (a >> k++) & 1 : null));
      const run = MT.runMacro(p, bits), ix = MT.fullIndex(p, run);
      const tag = JSON.stringify(nodes) + (ever ? " EVER" : "") + " a=" + a;
      if (ix.total !== MT.treeSize(p).vertices) fail(tag + ": index total " + ix.total + " vs treeSize " + MT.treeSize(p).vertices);
      const roots = [run.id.g.C, run.id["r" + M].A, run.id.b1.B, run.id.cA.C].concat(run.z !== null ? [run.z] : []);
      roots.forEach((root) => {
        let open = new Set(), view = MT.explore(ix, root, open, 3000), prev = check(view, ix, tag + " root " + root);
        // unfold random boxes step by step; earlier states must not change
        for (let step = 0; step < 14; step++) {
          const boxes = keysOf(view).filter((key) => view && true);
          if (!boxes.length) break;
          open.add(boxes[Math.floor(rnd() * boxes.length)]);
          const next = MT.explore(ix, root, open, 3000);
          const exr = check(next, ix, tag + " root " + root + " step " + step);
          Object.keys(prev.gid).forEach((key) => {
            const a1 = history(prev, key, Math.min(p.T + 6, 400)), a2 = history(exr, key, Math.min(p.T + 6, 400));
            if (a1 !== null && a2 !== null && a1 !== a2 && prev.res.changes !== undefined) {
              // a vertex that was a forced box before is simulated now; both must agree
              fail(tag + ": state of " + key + " changed after unfolding more");
            }
          });
          view = next; prev = exr;
        }
      });
      if (ix.total <= 6000) {
        const all = new Set(); all.all = true;
        const view = MT.explore(ix, run.id.g.C, all, 20000);
        let boxes = 0, shown = 0;
        (function walk(n) { if (n.box) boxes++; else shown++; n.children.forEach(walk); })(view.tree);
        if (boxes || shown !== ix.total) fail(tag + ": unfolding everything shows " + shown + " of " + ix.total + " with " + boxes + " boxes");
        check(view, ix, tag + " everything");
      }
    }
  });
});
console.log(JSON.stringify({ views: views, simulatedClockVertices: simulated, failures: failures }));
console.log(failures ? "EXPLORER TEST FAILED" : "EXPLORER TEST PASSED");
process.exitCode = failures ? 1 : 0;
