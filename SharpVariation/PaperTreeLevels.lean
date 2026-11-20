module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Ring

@[expose] public section
namespace SharpVariation.PaperTree

/-- The depth of the (s+1)-st branching child, denoted l_(s+1) in the paper. -/
def branchLevel : ℕ → ℕ
  | 0 => 2
  | s + 1 => 2 * branchLevel s + 1

theorem level_ge_two (t : ℕ) : 2 ≤ branchLevel t := by
  induction t with
  | zero => decide
  | succ t ih => simp only [branchLevel]; omega

theorem level_pos (t : ℕ) : 0 < branchLevel t := by
  have := level_ge_two t
  omega

theorem level_closed (t : ℕ) : branchLevel t + 1 = 3 * 2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [branchLevel, pow_succ, ← Nat.mul_assoc, ← ih]; omega

/-- Count the branching depths numbered zero through t which have been reached. -/
def stages : ℕ → ℕ → ℕ
  | 0, h => if branchLevel 0 ≤ h then 1 else 0
  | t + 1, h => if branchLevel (t+1) ≤ h then t+2 else stages t h

theorem stages_le (t h : ℕ) : stages t h ≤ t+1 := by
  induction t with
  | zero => rw [stages]; split <;> omega
  | succ t ih => rw [stages]; split <;> omega

theorem stages_mono (t : ℕ) : Monotone (stages t) := by
  intro x y hxy
  induction t with
  | zero => simp only [stages]; split <;> split <;> omega
  | succ t ih => simp only [stages]; split <;> split <;> first | omega | exact (stages_le t x).trans (by omega)

theorem stages_at_or_above (t h : ℕ) (hth : branchLevel t ≤ h) : stages t h = t+1 := by
  cases t <;> simp [stages, hth]

theorem stages_below_initial (t h : ℕ) (hsmall : h < 2) : stages t h = 0 := by
  induction t with
  | zero => simp [stages, branchLevel, Nat.not_le.mpr hsmall]
  | succ t ih =>
    have hlt : h < branchLevel (t+1) := lt_of_lt_of_le hsmall (level_ge_two _)
    simp [stages, Nat.not_le.mpr hlt, ih]

/-- Before the last cluster of leaves, doubling the depth can encounter at
most one additional branching stage. -/
theorem stages_half (t h : ℕ) : stages t h ≤ stages t (h/2)+1 := by
  induction t with
  | zero => exact (stages_le 0 h).trans (by omega)
  | succ t ih =>
    by_cases hth : branchLevel (t+1) ≤ h
    · have hhalf : branchLevel t ≤ h/2 := by rw [branchLevel] at hth; omega
      rw [stages_at_or_above _ _ hth]
      rw [stages]
      split
      · omega
      · rw [stages_at_or_above _ _ hhalf]
    · have hth' : ¬ branchLevel (t+1) ≤ h/2 := by omega
      simpa [stages, hth, hth'] using ih

/-- Depth of the final (quadratically branching) leaf cluster. -/
def height (t : ℕ) : ℕ := 2 * branchLevel t + 1

/-- At depth h there are k^(exponent t h) vertices in the paper's tree. -/
def exponent (t h : ℕ) : ℕ := if height t ≤ h then t+3 else stages t h

theorem exponent_mono (t : ℕ) : Monotone (exponent t) := by
  intro x y hxy
  have := stages_mono t hxy
  have := stages_le t x
  simp only [exponent]
  split <;> split <;> omega

theorem exponent_zero (t : ℕ) : exponent t 0 = 0 := by
  simp [exponent, height, stages_below_initial _ _ (by decide : 0 < 2)]

theorem exponent_one (t : ℕ) : exponent t 1 = 0 := by
  have h : ¬ height t ≤ 1 := by unfold height; have := level_pos t; omega
  simp [exponent, h, stages_below_initial _ _ (by decide : 1 < 2)]

theorem exponent_level (t : ℕ) : exponent t (branchLevel t) = t+1 := by
  have h : ¬ height t ≤ branchLevel t := by unfold height; omega
  simp [exponent, h, stages_at_or_above]

theorem exponent_next (t : ℕ) : exponent t (branchLevel t + 1) = t+1 := by
  have h : ¬ height t ≤ branchLevel t+1 := by unfold height; have := level_pos t; omega
  simp [exponent, h, stages_at_or_above]

theorem exponent_height (t : ℕ) : exponent t (height t) = t+3 := by simp [exponent]

theorem exponent_half (t h : ℕ) (hh : h < height t) :
    exponent t h ≤ exponent t (h/2)+1 := by
  have hh' : h/2 < height t := by omega
  simpa [exponent, Nat.not_le.mpr hh, Nat.not_le.mpr hh'] using stages_half t h

end SharpVariation.PaperTree
