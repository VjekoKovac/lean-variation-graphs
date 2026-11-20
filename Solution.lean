module

public import SharpVariation.CompleteModel
public import SharpVariation.Complete
public import SharpVariation.Four.Canonical
public import SharpVariation.PaperTree

@[expose] public section
noncomputable section
open Finset
namespace SharpVariation

/-- The complete-graph inequality, arXiv:2603.12462v1, Theorem 1. -/
theorem complete (n : ℕ) (hn : 3 ≤ n) (p : ℝ) (hp : 0 < p) (f : Fin n → ℝ) :
    variation (⊤ : SimpleGraph (Fin n)) p (maximal ⊤ f) ≤
      (1 - 1 / (n : ℝ)) * variation (⊤ : SimpleGraph (Fin n)) p f := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hc : 0 ≤ 1 - 1 / (n : ℝ) := sub_nonneg.mpr ((div_le_one hn0).mpr hn1)
  apply variation_le_of_energy_le hp hc
  let a : Fin n → ℝ := fun i => |f i|
  have h := complete_sum_le (univ : Finset (Fin n)) a (by simpa using (show 2 ≤ n by omega)) hp
  have hcomp : energy (⊤ : SimpleGraph (Fin n)) p (maximal ⊤ f) ≤
      (1 - 1 / (n : ℝ)) ^ p * energy (⊤ : SimpleGraph (Fin n)) p a := by
    simp only [energy_top p hp, maximal_top, CompleteGraph.energy, CompleteGraph.mean,
      card_univ, Fintype.card_fin, a] at h ⊢
    linarith
  exact hcomp.trans (mul_le_mul_of_nonneg_left (energy_abs_le ⊤ p hp.le f) (Real.rpow_nonneg hc _))

/-- The sharp constant on every connected four-vertex graph, Theorem 2. -/
theorem fourVertices.{u} {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hcard : Fintype.card W = 4) (hc : G.Connected) :
    IsLeast {c : ℝ | Admissible G 1 c} (3 / 4) := by
  let t := G.overFinIso hcard
  obtain ⟨k, hk, ⟨e⟩⟩ := Four.classify (G.overFin hcard) (t.connected_iff.mp hc)
  have same : {c : ℝ | Admissible G 1 c} = {c : ℝ | Admissible (Four.graphOfMask k) 1 c} := by
    ext c
    exact iso_admissible (t.trans e) hc 1 c
  rw [same]
  exact Four.representativeSharp hk

/-- A finite connected graph strictly exceeding any prescribed positive threshold,
Theorem 4. -/
theorem largeConst (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), G.Connected ∧
      ∃ f : W → ℝ, C * variation G p f < variation G p (maximal G f) := by
  exact PaperTree.large_witness p C hp hC

end SharpVariation
