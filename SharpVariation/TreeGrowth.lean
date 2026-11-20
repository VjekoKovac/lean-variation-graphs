module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace SharpVariation

/-- The last step of §5: after fixing m>p, the branching number k can be
chosen so that the contribution of the distinguished edges exceeds C^p.
The bound D on the ball size per unit branching is independent of k. -/
theorem tree_growth {m D : ℕ} {p C : ℝ} (hm : p < (m : ℝ)) (hp : 0 < p)
    (hD : 0 < D) (hC : 0 < C) :
    ∃ k : ℕ, 2 ≤ k ∧ D*k ≤ k^2 ∧
      C^p < ((k^m : ℕ) : ℝ) * (1 / ((D*k : ℕ) : ℝ) - 1 / ((k^2 : ℕ) : ℝ))^p := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  let T := C^p * (2 * (D : ℝ))^p
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 * (D : ℝ)) (T^((m:ℝ)-p)⁻¹))
  have hkD : 2 * (D : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hlarge := (Real.rpow_inv_lt_iff_of_pos hT (Nat.cast_nonneg k) (sub_pos.mpr hm)).mp
    ((le_max_right _ _).trans_lt hk)
  have hkN : 2 * D < k := by exact_mod_cast hkD
  have hkr : 0 < (k : ℝ) := by linarith
  have hdkn : D*k ≤ k^2 := by rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨k, by omega, hdkn, ?_⟩
  have hdiff : 1 / (2 * D * (k : ℝ)) ≤ 1 / (D * (k : ℝ)) - 1 / (k : ℝ)^2 := by
    field_simp
    nlinarith
  have hmain : C^p < (k : ℝ)^((m : ℝ) - p) / (2 * (D : ℝ))^p :=
    (lt_div_iff₀ (Real.rpow_pos_of_pos (by positivity) p)).mpr hlarge
  push_cast
  calc
    C^p < _ := hmain
    _ = (k : ℝ)^m * (1 / (2 * D * (k : ℝ)))^p := by
      rw [Real.rpow_sub hkr, Real.rpow_natCast, one_div, Real.inv_rpow (by positivity),
        Real.mul_rpow (by positivity) hkr.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hdiff hp.le) (by positivity)

end SharpVariation
