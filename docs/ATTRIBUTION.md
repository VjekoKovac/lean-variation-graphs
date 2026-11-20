# Mathematical sources and reused Lean proofs

The original source for this project is Cristian González-Riquelme, Vjekoslav Kovač, and José Madrid, *Sharp variational inequalities for the Hardy–Littlewood maximal operator on finite undirected graphs*, arXiv:2603.12462v1, 12 March 2026. The TeX labels are `thm:complete`, `thm:4vertices`, and `thm:largeconst`. [Versioned source](https://arxiv.org/abs/2603.12462v1)

The complete-graph proof in §2 cites González-Riquelme and Madrid for the convex-exponent case and for the single-high-vertex estimate, and cites Liu and Xue for the three-vertex starting case. The Lean proof supplies these parts within the project. See [the complete-graph guide](complete-graph.md), [the earlier paper by González-Riquelme and Madrid](https://arxiv.org/abs/2005.03146v3), and the bibliography of the original source.

The proof code uses the following previously formalized Mathlib results. They are imported from the Mathlib community's Apache-2.0 distribution at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Each link selects that revision.

| Role | Existing Lean proofs or definitions | Pinned source |
| --- | --- | --- |
| Graph distances and shortest paths | `SimpleGraph.dist`, `Connected.exists_path_of_dist`, `Reachable.exists_walk_length_eq_dist`, `dist_le`, `dist_top_of_ne` | [SimpleGraph/Metric.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Metric.lean) |
| Bounds on path length | `SimpleGraph.Walk.IsPath.length_lt` | [SimpleGraph/Paths.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Paths.lean) |
| Relabeling a graph on a finite type | `SimpleGraph.overFin` and `SimpleGraph.overFinIso` | [SimpleGraph/Maps.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Maps.lean) |
| Finite Jensen inequality in the convex range | `Real.rpow_arith_mean_le_arith_mean_rpow` | [MeanInequalitiesPow.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/MeanInequalitiesPow.lean) |
| Power concavity for subunit exponents | `Real.concaveOn_rpow` | [SpecificFunctions/Pow.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean) |
| Finite Jensen in the concave range | `ConcaveOn.le_map_sum` | [Jensen.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Convex/Jensen.lean) |
| Two-term Hölder | `Real.inner_le_Lp_mul_Lq_of_nonneg` | [MeanInequalities.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/MeanInequalities.lean) |
| Concave Bernoulli bound | `rpow_one_add_le_one_add_mul_self` | [SpecificFunctions/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean) |
| Explicit numerical constant | `Real.exp_one_lt_three` | [ExponentialBounds.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/ExponentialBounds.lean) |
| Monotonicity and manipulation of real powers | `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_sub` | [Pow/Real.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean) |

The four-vertex dual certificates were generated for this formalization. The source paper's Mathematica computations motivate the linear-programming argument. Lean checks the explicit inequalities with Mathlib's `linear_combination` tactic and checks the finite tables by kernel reduction. None of the three targets depends on output from Mathematica, Python, or a native decision procedure.

The repository structure was inspired by the DFR formalization and the Palomar starter project. No DFR theorem is invoked in these graph proofs. [DFR repository](https://github.com/roos-j/lean-dfr) · [Palomar's project guidance](https://palomar-registry.org/how-to-submit)
