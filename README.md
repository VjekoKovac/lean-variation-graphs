# Sharp variational inequalities on finite graphs

Lean 4 formalization of three introduction theorems from *Sharp variational inequalities for the Hardy–Littlewood maximal operator on finite undirected graphs*, by Cristian González-Riquelme, Vjekoslav Kovač, and José Madrid. The formalization authors are the same three authors, as specified by the requester. Codex generated the Lean code and ran the documented AI reviews. [Original paper, arXiv:2603.12462v1](https://arxiv.org/abs/2603.12462v1) · [Full text](https://arxiv.org/html/2603.12462v1)

| Paper | Lean declaration | Result |
| --- | --- | --- |
| Theorem 1 | `SharpVariation.complete` | For every integer n ≥ 3, every real p > 0 and every real-valued function on the complete graph, the p-variation of its centered maximal function is at most (1 − 1/n) times its p-variation. The separate lemma `SharpVariation.complete_spike` verifies sharpness. |
| Theorem 2 | `SharpVariation.fourVertices` | For **every** connected simple graph on four vertices, 3/4 is the least nonnegative coefficient in the 1-variation inequality. |
| Theorem 4 | `SharpVariation.largeConst` | For every real p > 0 and C > 0 there is a finite connected simple graph and a real-valued input for which the output p-variation strictly exceeds C times the input p-variation. |

Observation 3 concerns graphs on five vertices. Its computational evidence and the paper's conjecture on paths lie outside these three statements.

**Verification.** Lean Comparator matched all three declarations to the reviewed Challenge. Lean’s default kernel, NanoDa, and con-ron accepted the solution. Each of the three headline theorems depends on exactly `propext`, `Classical.choice`, and `Quot.sound`. The [comparison transcript](verification/comparator.log) and [axiom report](verification/axioms.log) record the actual checks. Project publication and Palomar registration are pending.

## Start here if you are new to Lean

1. Install Visual Studio Code and its official **Lean 4** extension. Complete **Documentation → Show Setup Guide** in the Lean extension. [Official installation guide](https://lean-lang.org/install/)
2. Extract the ZIP into an ordinary folder. In VS Code choose **File → Open Folder** and open the folder containing `lean-toolchain` and `lakefile.toml`. Opening the whole folder lets Lean resolve project imports.
3. In the VS Code terminal, run the following commands one at a time. The first command downloads the pinned libraries, the second builds the solution and the supplementary lemmas, and the third prints the axioms on which the public theorems depend. The initial download can take several minutes.

```sh
lake exe cache get
lake build
lake env lean Axioms.lean
```

4. Open [Challenge.lean](Challenge.lean). Read `closedBall`, `ballAverage`, `maximal`, `energy`, and `variation` in order. In `fourVertices`, hover over `IsLeast` and `Admissible` to see the upper bound and its optimality. The three reference declarations end in `by sorry` so this file can state exactly what the independent solution must prove. Its three warnings are expected. [Solution.lean](Solution.lean) has a separate import chain with checked proofs.
5. Open [Solution.lean](Solution.lean), place the cursor after a line inside a proof, and open the Lean Infoview to see its hypotheses and current goal. Use **Go to Definition** on `complete_sum_le` to follow the split at p = 1. For a concrete four-vertex example, start with the path in [the four-vertex guide](docs/four-vertices.md) before opening a generated certificate.

## Proofs and verification

The project uses Lean 4.35.0 and Mathlib v4.35.0. The manifest pins Mathlib and its transitive dependencies. The file [comparator.json](comparator.json) names all three public declarations and permits `propext`, `Classical.choice`, and `Quot.sound`. Comparator compares the self-contained Challenge and the independently compiled Solution. It checks both the statements and the definitions on which they depend. The solution's dependency reports are in [verification](verification).

- [Finite graph definitions](SharpVariation/Defs.lean) and [graph lemmas](SharpVariation/Graph.lean) implement the definitions preceding Theorem 1. The graph lemmas justify the finite cut-off on ball radii and relabeling invariance.
- [The original rooted-tree proof](docs/paper-tree.md) derives the two ball-size bounds at adjacent vertices, counts the distinguished edges, and makes the final choice of branching number explicit.
- [Sharp constants](SharpVariation/Constants.lean) states the three consequences for the literal extended-nonnegative optimal coefficient. [Radii.lean](SharpVariation/Radii.lean) proves that all real radii produce exactly the maximum used in the Challenge.
- [Complete-graph proof](docs/complete-graph.md) and [the incident-edge estimate](docs/incident-estimate.md) describe the induction and the argument for Proposition 6.
- [Four-vertex computation](docs/four-vertices.md) gives the edge lists, rational certificates, and equality witnesses. The standard build uses the committed Lean certificates. The optional independent integer cross-check is `python3 scripts/crosscheck_four.py`.
- [Sources and reused Mathlib proofs](docs/ATTRIBUTION.md) identifies the imported results and the pinned code for each.
- [Independent AI statement review](docs/REVIEW.md) and [AI proof review](docs/proof-review.md) explain what the reviewers compared with the source.

On Linux with bubblewrap installed, repeat the comparison from the project root. GitHub Actions runs the same verification. On Windows you can run the ordinary Lean build locally and use Actions for the Linux comparison.

```sh
bash scripts/verify.sh
```

## Publish the repository and submit the checked revision

Create an empty public GitHub repository. A suggested name is `lean-sharp-variation-graphs`. Leave GitHub's README and license initialization unchecked because both files are already present here. From the extracted project folder, run the following commands, using your new repository URL on the fourth line.

```sh
git init -b main
git add .
git commit -m "Formalize sharp variational inequalities on finite graphs"
git remote add origin https://github.com/YOUR-ACCOUNT/lean-sharp-variation-graphs.git
git push -u origin main
git rev-parse HEAD
```

If Git asks for an author identity at the commit step, set it in this repository with `git config user.name "Your name"` and `git config user.email "your GitHub email"`, then repeat the commit.

Extract the archive directly into your repository folder. GitHub should show `.github/workflows/verify.yml` and `formalization.yaml` at exactly those paths. With GitHub Actions enabled, the first push containing that file queues **Actions → Lean build**. A commit made in GitHub’s browser editor also triggers it. In VS Code, use **Sync Changes** or `git push` after committing locally. In the run for your commit, **Lean build** compiles the project and prints the axiom report. **Lean Comparator** runs after that job succeeds. Push the extracted files, including the hidden `.github` folder. On the Palomar submission form, enter the public repository URL and the full 40-character commit printed by the last command. Keep the project-directory, Comparator-path, and metadata-path fields at their defaults. On the form, give your relationship to the formalization, verify GitHub write access, and save the status-page URL. After a successful review, choose **Register** on that page to publish the record. The registry uses the immutable commit you supplied. If you change the public description or proof, commit and push the edit and submit its new SHA. [Palomar submission instructions](https://palomar-registry.org/how-to-submit) · [Example GitHub project](https://github.com/roos-j/lean-dfr) · [Example Palomar record](https://palomar-registry.org/entry?id=PALOMAR-2026-10-21-000004&version=1)

The repository uses the Apache-2.0 license, matching the example project. The paper is cited as the mathematical source. Review the public metadata, authorship, maintainership, and license before publishing.
