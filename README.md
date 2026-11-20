# Sharp variational inequalities on finite graphs

Lean 4 formalization of three introduction theorems from *Sharp variational inequalities for the Hardy–Littlewood maximal operator on finite undirected graphs*, by Cristian González-Riquelme, Vjekoslav Kovač, and José Madrid. The formalization authors are the same three authors, as specified by the requester. Codex generated the Lean code and ran the documented AI reviews. [Original paper, arXiv:2603.12462v1](https://arxiv.org/abs/2603.12462v1) · [Full text](https://arxiv.org/html/2603.12462v1)

| Paper | Lean declaration | Result |
| --- | --- | --- |
| Theorem 1 | `SharpVariation.complete` | For every integer n ≥ 3, every real p > 0 and every real-valued function on the complete graph, the p-variation of its centered maximal function is at most (1 − 1/n) times its p-variation. The separate lemma `SharpVariation.complete_spike` verifies sharpness. |
| Theorem 2 | `SharpVariation.fourVertices` | For **every** connected simple graph on four vertices, 3/4 is the least nonnegative coefficient in the 1-variation inequality. |
| Theorem 4 | `SharpVariation.largeConst` | For every real p > 0 and C > 0 there is a finite connected simple graph and a real-valued input for which the output p-variation strictly exceeds C times the input p-variation. |

Observation 3 concerns graphs on five vertices. Its computational evidence and the paper's conjecture on paths lie outside these three statements.

**Verification.** Lean Comparator matched all three declarations to the reviewed Challenge. Lean’s default kernel, NanoDa, and con-ron accepted the solution. Each of the three headline theorems depends on exactly `propext`, `Classical.choice`, and `Quot.sound`. The [comparison transcript](verification/comparator.log) and [axiom report](verification/axioms.log) record the actual checks. Project publication and Palomar registration are pending.

## Proofs and verification

The project uses Lean 4.35.0 and Mathlib v4.35.0. The manifest pins Mathlib and its transitive dependencies. The file [comparator.json](comparator.json) names all three public declarations and permits `propext`, `Classical.choice`, and `Quot.sound`. Comparator compares the self-contained Challenge and the independently compiled Solution. It checks both the statements and the definitions on which they depend. The solution's dependency reports are in [verification](verification).

- [Finite graph definitions](SharpVariation/Defs.lean) and [graph lemmas](SharpVariation/Graph.lean) implement the definitions preceding Theorem 1. The graph lemmas justify the finite cut-off on ball radii and relabeling invariance.
- [The original rooted-tree proof](docs/paper-tree.md) derives the two ball-size bounds at adjacent vertices, counts the distinguished edges, and makes the final choice of branching number explicit.
- [Sharp constants](SharpVariation/Constants.lean) states the three consequences for the literal extended-nonnegative optimal coefficient. [Radii.lean](SharpVariation/Radii.lean) proves that all real radii produce exactly the maximum used in the Challenge.
- [Complete-graph proof](docs/complete-graph.md) and [the incident-edge estimate](docs/incident-estimate.md) describe the induction and the argument for Proposition 6.
- [Four-vertex computation](docs/four-vertices.md) gives the edge lists, rational certificates, and equality witnesses. The standard build uses the committed Lean certificates. The optional independent integer cross-check is `python3 scripts/crosscheck_four.py`.
- [Sources and reused Mathlib proofs](docs/ATTRIBUTION.md) identifies the imported results and the pinned code for each.
- [Independent AI statement review](docs/REVIEW.md) and [AI proof review](docs/proof-review.md) explain what the reviewers compared with the source.

The repository uses the Apache-2.0 license, matching the example project. The paper is cited as the mathematical source. Review the public metadata, authorship, maintainership, and license before publishing.
