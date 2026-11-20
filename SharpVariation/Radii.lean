module

public import SharpVariation.Graph
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
noncomputable section
open Finset
namespace SharpVariation
variable {V : Type*} [Fintype V]

/-- The closed ball at a nonnegative real radius is the closed ball at its natural floor. -/
theorem real_ball_eq_closedBall (G : SimpleGraph V) (v : V) (r : ℝ) (hr : 0 ≤ r) :
    (Finset.univ.filter fun w => (G.dist v w : ℝ) ≤ r) = closedBall G v ⌊r⌋₊ := by
  ext w
  simp [Nat.le_floor_iff hr]

/-- The finite maximum in the challenge attains the maximum over all
nonnegative real radii in the paper. -/
theorem maximal_real_radii {G : SimpleGraph V} (hc : G.Connected) (f : V → ℝ) (v : V) :
    IsGreatest {y : ℝ | ∃ r : ℝ, 0 ≤ r ∧ y = ballAverage G f v ⌊r⌋₊} (maximal G f v) := by
  constructor
  · obtain ⟨i, _, hi⟩ := (range (Fintype.card V + 1)).exists_mem_eq_sup'
      (show (range (Fintype.card V + 1)).Nonempty from ⟨0, mem_range.mpr (by omega)⟩)
      (ballAverage G f v)
    exact ⟨(i : ℝ), Nat.cast_nonneg i, by simpa [maximal] using hi⟩
  · rintro _ ⟨r, _, rfl⟩
    exact ballAverage_le_maximal hc f v _

end SharpVariation
