module

public import SharpVariation.CompleteModel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
open Finset
namespace SharpVariation

/-- Equality witness for the sharpness remark following Theorem 1.
The value is one at the distinguished vertex and zero elsewhere. -/
theorem complete_spike (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 0 < p) (a : Fin n) :
    let f : Fin n → ℝ := fun i => if i = a then 1 else 0
    0 < variation (⊤ : SimpleGraph (Fin n)) p f ∧
      variation (⊤ : SimpleGraph (Fin n)) p (maximal ⊤ f) =
      (1 - 1 / (n : ℝ)) * variation (⊤ : SimpleGraph (Fin n)) p f := by
  classical
  let f : Fin n → ℝ := fun i => if i = a then 1 else 0
  let c := 1 - 1 / (n : ℝ)
  change 0 < variation (⊤ : SimpleGraph (Fin n)) p f ∧ _ = c * _
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hdiv : 1 / (n : ℝ) ≤ 1 := by rw [div_le_iff₀ hn0]; linarith
  have hc : 0 ≤ c := sub_nonneg.mpr hdiv
  have hsum : ∑ i, |f i| = 1 := by
    simp [f, apply_ite abs]
  have hm (i : Fin n) : maximal (⊤ : SimpleGraph (Fin n)) f i = c * f i + 1 / n := by
    rw [maximal_top, hsum, Fintype.card_fin]
    by_cases hi : i = a
    · simpa [f, hi, c] using hdiv
    · simp [f, hi]
  have he : energy (⊤ : SimpleGraph (Fin n)) p (maximal ⊤ f) =
      c ^ p * energy (⊤ : SimpleGraph (Fin n)) p f := by
    simp only [energy_top _ hp, hm, add_sub_add_right_eq_sub, ← mul_sub, abs_mul,
      abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _), ← Finset.mul_sum]
    ring
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b ≠ a := by
    let b₀ : Fin n := ⟨0, by omega⟩
    let b₁ : Fin n := ⟨1, by omega⟩
    by_cases h : b₀ = a
    · exact ⟨b₁, fun h' => by have := congrArg Fin.val (h'.trans h.symm); simp [b₀, b₁] at this⟩
    · exact ⟨b₀, h⟩
  have hpos : 0 < energy (⊤ : SimpleGraph (Fin n)) p f := by
    rw [energy_top _ hp]
    apply div_pos _ (by norm_num)
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
    refine ⟨a, mem_univ _, Finset.sum_pos' (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) ?_⟩
    exact ⟨b, mem_univ _, by simp [f, hb]⟩
  refine ⟨Real.rpow_pos_of_pos hpos _, ?_⟩
  rw [variation, he, Real.mul_rpow (Real.rpow_nonneg hc _) hpos.le, ← Real.rpow_mul hc,
    show p * (1 / p) = 1 by field_simp, Real.rpow_one]
  rfl

end SharpVariation
