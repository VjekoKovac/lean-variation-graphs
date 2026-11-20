module

public import SharpVariation.Graph

@[expose] public section
noncomputable section
open Finset
namespace SharpVariation
variable {V : Type*} [Fintype V]

private theorem closedBall_top_zero (v : V) :
    closedBall (⊤ : SimpleGraph V) v 0 = {v} := by
  classical
  ext w
  by_cases h : v = w
  · subst w; simp
  · simp [SimpleGraph.dist_top_of_ne h, Ne.symm h]

private theorem closedBall_top_succ (v : V) (r : ℕ) :
    closedBall (⊤ : SimpleGraph V) v (r+1) = univ := by
  ext w
  by_cases h : v = w
  · subst w; simp
  · simp [SimpleGraph.dist_top_of_ne h]

/-- On a complete graph the only candidate averages are the value and the global mean. -/
theorem maximal_top (f : V → ℝ) (v : V) : maximal ⊤ f v =
    max |f v| ((∑ w, |f w|) / Fintype.card V) := by
  classical
  have h0 : ballAverage ⊤ f v 0 = |f v| := by simp [ballAverage, closedBall_top_zero]
  have hs (r : ℕ) : ballAverage ⊤ f v (r+1) = (∑ w, |f w|) / Fintype.card V := by
    simp [ballAverage, closedBall_top_succ]
  have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold maximal
  apply le_antisymm
  · apply sup'_le
    intro r _
    cases r with
    | zero => rw [h0]; exact le_max_left _ _
    | succ r => rw [hs]; exact le_max_right _ _
  · apply max_le
    · rw [← h0]
      exact le_sup' _ (mem_range.mpr (by omega))
    · rw [← hs 0]
      exact le_sup' _ (mem_range.mpr (by omega))

theorem energy_top (p : ℝ) (hp : 0 < p) (f : V → ℝ) :
    energy (⊤ : SimpleGraph V) p f = (∑ v, ∑ w, |f v - f w| ^ p) / 2 := by
  classical
  unfold energy
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases h : i = j <;> simp_all [Real.zero_rpow hp.ne']

end SharpVariation
