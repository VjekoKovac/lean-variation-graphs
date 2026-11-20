module

public import SharpVariation.Defs
public import SharpVariation.Four.Tools
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace SharpVariation.Four

open Finset

/-- On four vertices the definition inspects just five integer radii. -/
theorem maximal_four (G : SimpleGraph (Fin 4)) (f : Fin 4 → ℝ) (i : Fin 4) :
    maximal G f i = max (ballAverage G f i 0) (max (ballAverage G f i 1)
      (max (ballAverage G f i 2) (max (ballAverage G f i 3) (ballAverage G f i 4)))) := by
  unfold maximal
  change (range 5).sup' _ _ = _
  let a := ballAverage G f i
  have h (k : ℕ) (hk : k < 5) := Finset.le_sup' (s := range 5) a (mem_range.mpr hk)
  apply le_antisymm
  · apply Finset.sup'_le
    intro k hk
    have hk' := mem_range.mp hk
    interval_cases k <;> simp [le_max_iff]
  · simp only [max_le_iff]
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩

/-- Taking the pointwise absolute value contracts each edge difference. -/
theorem abs_contract (f : Fin 4 → ℝ) (i j : Fin 4) : |(|f i| - |f j|)| ≤ |f i - f j| :=
  abs_abs_sub_abs_le_abs_sub _ _

end SharpVariation.Four
