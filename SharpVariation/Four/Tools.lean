module
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Elementary ways of recording all possibilities for a maximum and an absolute value. -/
namespace SharpVariation.Four

theorem absChoice (a : ℝ) : |a| = a ∨ |a| = -a := by
  rcases le_total 0 a with h | h
  · exact Or.inl (abs_of_nonneg h)
  · exact Or.inr (abs_of_nonpos h)

theorem maxBounds2 (y a b : ℝ) (h : y = max a b) :
    a ≤ y ∧ b ≤ y ∧ (y ≤ a ∨ y ≤ b) := by
  subst y
  exact ⟨le_max_left .., le_max_right .., (le_total a b).elim
    (fun h => Or.inr (max_le h le_rfl)) (fun h => Or.inl (max_le le_rfl h))⟩

theorem maxBounds3 (y a b c : ℝ) (h : y = max a (max b c)) :
    a ≤ y ∧ b ≤ y ∧ c ≤ y ∧ (y ≤ a ∨ y ≤ b ∨ y ≤ c) := by
  rcases maxBounds2 _ _ _ h with ⟨ha, hbc, ha' | hbc'⟩
  all_goals refine ⟨ha, le_trans (le_max_left ..) hbc, le_trans (le_max_right ..) hbc, ?_⟩
  · exact Or.inl ha'
  · exact Or.inr ((maxBounds2 _ _ _ (rfl : max b c = _)).2.2.imp (le_trans hbc') (le_trans hbc'))

theorem maxBounds4 (y a b c d : ℝ) (h : y = max a (max b (max c d))) :
    a ≤ y ∧ b ≤ y ∧ c ≤ y ∧ d ≤ y ∧ (y ≤ a ∨ y ≤ b ∨ y ≤ c ∨ y ≤ d) := by
  obtain ⟨ha, hrest, h'⟩ := maxBounds2 _ _ _ h
  obtain ⟨hb, hc, hd, h''⟩ := maxBounds3 _ _ _ _ (rfl : max b (max c d) = _)
  refine ⟨ha, hb.trans hrest, hc.trans hrest, hd.trans hrest, ?_⟩
  rcases h' with h' | h'
  · exact Or.inl h'
  · exact Or.inr (h''.imp (le_trans h') (fun t => t.imp (le_trans h') (le_trans h')))

end SharpVariation.Four
