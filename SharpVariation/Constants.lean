module

public import Solution
public import SharpVariation.Optimal
public import SharpVariation.Spike

@[expose] public section
noncomputable section
open scoped ENNReal
namespace SharpVariation

/-- Theorem 1 together with the point-mass equality example in the following paragraph. -/
theorem optimal_complete (n : ℕ) (hn : 3 ≤ n) (p : ℝ) (hp : 0 < p) :
    optimalConstant (⊤ : SimpleGraph (Fin n)) p = ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
  apply optimalConstant_of_isLeast
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnon : 0 ≤ 1 - 1 / (n : ℝ) :=
    sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hn1)).mpr hn1)
  refine ⟨⟨hnon, complete n hn p hp⟩, ?_⟩
  intro c hc
  let a : Fin n := ⟨0, by omega⟩
  let f : Fin n → ℝ := fun i => if i = a then 1 else 0
  obtain ⟨hv, he⟩ := complete_spike n (by omega) p hp a
  have h := hc.2 f
  change variation ⊤ p (maximal ⊤ f) = _ at he
  rw [he] at h
  exact le_of_mul_le_mul_right h hv

/-- The literal sharp-constant equality of Theorem 2. -/
theorem optimal_fourVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : Fintype.card V = 4) (hc : G.Connected) :
    optimalConstant G 1 = ENNReal.ofReal (3 / 4) :=
  optimalConstant_of_isLeast (fourVertices G hn hc)

/-- The literal sharp-constant formulation of Theorem 4, allowing an infinite optimum. -/
theorem optimal_largeConst (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.Connected ∧
      ENNReal.ofReal C < optimalConstant G p := by
  obtain ⟨V, inst, G, hG, f, hf⟩ := largeConst p C hp hC
  exact ⟨V, inst, G, hG, lt_optimalConstant_of_witness hC.le f hf⟩

end SharpVariation
