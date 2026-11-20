module

public import SharpVariation.Graph
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section
noncomputable section
open scoped ENNReal
namespace SharpVariation
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The paper's extended nonnegative optimal coefficient: take the infimum of
all finite admissible coefficients, with empty infimum equal to infinity. -/
def optimalConstant (G : SimpleGraph V) (p : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {c : ℝ | Admissible G p c})

theorem optimalConstant_of_isLeast {p c : ℝ} (hc : IsLeast {d : ℝ | Admissible G p d} c) :
    optimalConstant G p = ENNReal.ofReal c := by
  unfold optimalConstant
  apply le_antisymm
  · apply sInf_le
    exact ⟨c, hc.1, rfl⟩
  exact le_sInf fun _ ⟨d, hd, he⟩ => he ▸ ENNReal.ofReal_le_ofReal (hc.2 hd)

/-- A single strict violation gives a strict lower bound for the infimum.
For positive input variation its ratio gives a uniform lower bound for every
admissible coefficient. This includes the possibility of an infinite optimum. -/
theorem lt_optimalConstant_of_witness {p c : ℝ} (hc : 0 ≤ c) (f : V → ℝ)
    (hf : c * variation G p f < variation G p (maximal G f)) :
    ENNReal.ofReal c < optimalConstant G p := by
  have hv : 0 ≤ variation G p f := Real.rpow_nonneg (energy_nonneg ..) _
  rcases eq_or_lt_of_le hv with h | h
  · have emp : {d : ℝ | Admissible G p d} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hbound := hd.2 f
      rw [← h, mul_zero] at hf hbound
      exact (not_lt_of_ge hbound) hf
    simp [optimalConstant, emp]
  · let ratio := variation G p (maximal G f) / variation G p f
    have hcr : c < ratio := (lt_div_iff₀ h).mpr hf
    refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).mpr hcr) ?_
    apply le_sInf
    rintro y ⟨d, hd, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ h).mpr (hd.2 f))

end SharpVariation
