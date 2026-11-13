# Majority on trees

Interactive companion to the project's research notes on synchronous majority dynamics on trees
(`research/majority-degree-20261006/`, October 2026).

**The result.** Predicting synchronous majority is P-complete even on trees of maximum degree 5,
with all degrees odd. Here every vertex takes the majority of its neighbours and keeps its state on
a tie. The proof is analytic, with internal review between agents; it is not a peer-reviewed
publication. This site re-implements the construction and checks it by direct simulation.

The **Gadgets** tab shows, step by step, the pieces of the reduction:

- **Clocks.**
  - Constants (cherries) and two-arm timers.
  - Pulses P[a,b) and their complements.
  - The node with a rotating dissident.
  - The complete word generator of degree 5.
- **Memory and program.**
  - A macrocell A – C – B in its modes HOLD, RESET, LOAD and COPY.
  - The 27 steps of GATE, which compute AND or OR in macrocell g.

Every frame is an exact state of the dynamics. For every clock you can choose how its consumer
behaves, including an adversary that always votes against the next bit; the port follows its word
anyway. Each gadget can be downloaded as a tree with its initial configuration (JSON or edge list).

The **Circuit compiler** tab takes a Boolean circuit, given as an adjacency matrix or as a list of
gates, and builds the tree of the reduction:

- macrocells for a bus and its registers;
- the serial program that reads, combines and writes every gate;
- the control words played by the clocks.

It runs the macrocells for any input assignment and lets you follow the program instruction by
instruction. It also checks every assignment, and the plan of the tree can be downloaded.

A **Full tree** view shows the whole graph without the macrocell summary, unfolded on demand from
any vertex of a macrocell, down to every vertex of every clock.

## View it

Open `index.html` in a browser. It works directly from disk, offline, and from any folder. There is
no build step and there are no external resources. The same site as one file:
`dist/majority-trees.html`.

To publish it, upload the folder (or only `dist/majority-trees.html`) to any static host, for
example GitHub Pages or CodeFloe Pages. All links are relative. In `index.html`, `SITE_CONFIG` takes
optional links to the notes, the code and the public address of the site.

## Circuit compiler

### From a circuit to a tree

1. **Lowering.** The circuit is rewritten with AND and OR gates only, as in the two-dimensional
   compiler: negations are pushed to the inputs, and XOR and XNOR are expanded. The inputs, with
   their values, become constant nodes; the gates follow in order, each computed from two earlier
   nodes. The output is the last node, M.
2. **Macrocells.** There are 3M + 5 of them:
   - the bus g – b<sub>1</sub> – … – b<sub>M</sub>;
   - an arm b<sub>i</sub> – c<sub>i</sub> – r<sub>i</sub> for every node; register r<sub>i</sub>
     keeps the value of node i behind its connector c<sub>i</sub>;
   - two working arms g – c<sub>A</sub> – r<sub>A</sub> and g – c<sub>B</sub> – r<sub>B</sub>.

   A macrocell is a path A – C – B with a leaf on each end. Each main vertex has one external
   port, two controls and two memory neighbours, so its degree is 5. Unused ports carry a
   constant-0 cherry.
3. **Program.** For every gate i with operands p and q, the program does
   READ(p, A), READ(q, B), GATE, WRITE(i) and clears the temporaries. That takes
   12(p + q + i) + 147 steps. Every step says how many controls of each main vertex are 1:
   - u = 0: the vertex computes the AND of its three other neighbours (RESET);
   - u = 1: their majority (HOLD);
   - u = 2: their OR (LOAD).
4. **Clocks.** Control j of a vertex plays the word [j ≤ u(t)]. A private degree-5 generator plays
   that word after the common delay S = ⌈log₂(H + 2)⌉ + 8, with H = 200M² + 200. The output
   register holds the value of the circuit from the end of the program on, and it is read at
   T = S + H.
5. **EVER receiver.** The optional receiver z, attached to the output register, becomes 1 at
   T + 2 if and only if the output is 1, and is 0 before.

### What the page simulates

The full tree is very large. Every control is a generator of up to hundreds of millions of
vertices, and two nodes already give about 5 · 10⁷ vertices; the page shows its exact size. The
page therefore simulates the **macrocell level** exactly:

- macrocells, leaves, constant ports and the receiver follow the rule;
- each control follows its word, which is exactly what its generator guarantees, against any
  behaviour of the macrocell.

Where nothing changes, the simulation jumps ahead. For every run the page checks the following:

- every macrocell is quiescent with the right register contents before the program, after every
  gate and at T;
- the output at T;
- the receiver.

### The full tree

The **Full tree** card shows every vertex of the tree, starting at any vertex of a macrocell.

- **Boxes.** A box is the whole subtree behind one edge. It shows its number of vertices and is
  colored by the state of its first vertex. Selecting a box unfolds it one level; selecting an
  unfolded vertex folds it again.
- **Clock subtrees.** A control unfolds into its generator: nodes with a rotating dissident, then
  pulses, timers, timer arms and constants, down to single vertices. The inspector of a macrocell
  has an **Unfold** button for each control.
- **States.** States are exact. Macrocell vertices come from the macrocell run. The unfolded clock
  vertices are simulated with the majority rule, together with the vertex they hang from. A folded
  subtree touches the rest through one edge, so it is replaced by the proven history of its first
  vertex. The page checks that every simulated clock vertex follows its proven history, and says
  so.
- **Unfold everything.** This is possible when the tree has at most 6000 vertices: circuits that
  reduce to one node, such as NOT(NOT(a)), which has 3556 vertices with the receiver.

### Downloads

- **Plan (.json).** Macrocells, ports, constant ports, the receiver, and the history of every
  control (initial bit and change times, delay included), for the chosen inputs.
- **Macrocell tree (.json).** The exact tree the page simulates. The controls are forced vertices
  given by their change times.
- **View (.svg).** The current picture.

`tools/expand_tree.py` writes the **full** tree of a plan, every vertex and edge, as text.
`--check` also simulates it directly and compares the output register and z with the circuit:

```sh
python3 -B tools/expand_tree.py majority-tree-plan.json --check
```

## How the construction was checked

The construction of `research/majority-degree-20261006/` was re-implemented independently in
Python (`research/degree5-check-20261007/deg5.py`). It was simulated with a generic simulator of
the majority rule (`majsim.c`): 1193 tests, 0 failures. They cover:

- pulses for all 1 ≤ a < b ≤ 40, against five consumers, adversarial ones included;
- generators of every word with up to 10 bits, and sampled words with up to 64 changes;
- the macrocell modes against arbitrary ports;
- the whole program, with every input assignment and the EVER receiver, for every circuit with up
  to four nodes and random circuits with up to twelve;
- complete trees with real generators for small circuits, compared vertex by vertex with the
  macrocell level.

See `research/degree5-check-20261007/REVIEW.md`.

This page's model (`assets/tree-model.js`) is a second, independent implementation in
JavaScript. `tools/test_model.cjs` compares it with the Python one through `tools/reference.json`:

- the structure and size of the generator of 1048 words, and the port of the tree against an
  adversarial consumer;
- for 116 circuit plans: L, H, S, T, the gate checkpoints, every control history and the size of
  the full tree;
- for 380 runs: the exact history of every macrocell vertex, identical bit for bit to the Python
  run, and the checks above.

`tools/test_explorer.cjs` tests the full-tree view in 2704 views:
- shown vertices plus folded boxes always add up to the size of the tree;
- every unfolded clock vertex follows its proven history;
- unfolding more never changes what was already shown;
- small trees unfold completely.

```sh
node tools/test_model.cjs                 # the page's model against the Python reference
node tools/test_explorer.cjs              # the full-tree view
python3 -B tools/make_reference.py        # regenerate tools/reference.json (about 2 minutes)
python3 -B tools/build_standalone.py      # dist/majority-trees.html
```

`tools/generator/` holds copies of the Python implementation and of the simulator, with their
SHA-256 in `PROVENANCE.sha256`.

## Files

| Path | Content |
| --- | --- |
| `index.html` | The page. |
| `assets/tree-model.js` | The construction and the simulator (no DOM; also used by the tests in Node). |
| `assets/tree-draw.js` | SVG drawing of trees and bit strips. |
| `assets/app.js` | The Gadgets tab. |
| `assets/compiler.js` | The Circuit compiler tab. |
| `assets/circuit-input.js` | Circuit editor formats, shared with the two-dimensional site. |
| `assets/style.css` | Styles, shared with the two-dimensional site. |
| `tools/test_model.cjs` | Model test against the Python reference. |
| `tools/test_explorer.cjs` | Tests of the full-tree view. |
| `tools/make_reference.py` | Writes `tools/reference.json` from `tools/generator/deg5.py`. |
| `tools/expand_tree.py` | Full tree of a downloaded plan, with an optional direct simulation. |
| `tools/build_standalone.py` | Single-file version. |
| `tools/generator/` | Python implementation and simulator, with provenance. |
| `dist/majority-trees.html` | The site in one file. |

## License

To be decided by the authors.
