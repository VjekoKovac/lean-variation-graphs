module
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import SharpVariation.PaperHolder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The incident-edge estimate for subunit exponents

This file formalizes Proposition 6 of González-Riquelme–Kovač–Madrid.
The concentration of the low values is proved by the chord inequality for a
concave power. We then use the paper's uniform Jensen and two-term Hölder
argument; explicit weights prove its scalar coefficient budget.
-/

open scoped BigOperators

namespace SharpVariation

/-- Concentrating all of the excess over a common floor at one point minimizes
the sum of concave powers. This is the Karamata step of the paper. -/
theorem concentrate_rpow {ι : Type*} (t : Finset ι) (y : ι → ℝ)
    {u p : ℝ} (hu : 0 ≤ u) (hy : ∀ i ∈ t, u ≤ y i)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (u + ∑ i ∈ t, (y i - u)) ^ p + ((t.card : ℝ) - 1) * u ^ p ≤
      ∑ i ∈ t, y i ^ p := by
  let z := ∑ i ∈ t, (y i - u)
  have hz : 0 ≤ z := Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (hy i hi))
  have hbound (i) (hi : i ∈ t) : y i - u ≤ z :=
    Finset.single_le_sum (fun j hj => sub_nonneg.mpr (hy j hj)) hi
  change (u + z) ^ p + _ ≤ _
  rcases hz.eq_or_lt with hzero | hpos
  · have heq (i) (hi : i ∈ t) : y i = u := by
      have := hbound i hi
      linarith [hy i hi]
    rw [Finset.sum_congr rfl (fun i hi => congrArg (fun a : ℝ => a ^ p) (heq i hi))]
    simp [← hzero]
    ring_nf
    rfl
  · let b (i : ι) := (y i - u) / z
    have hsum : ∑ i ∈ t, b i = 1 := by
      simp only [b, div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ hpos.ne'
    have hpoint (i) (hi : i ∈ t) :
        u ^ p + b i * ((u + z) ^ p - u ^ p) ≤ y i ^ p := by
      have hb : 0 ≤ b i := div_nonneg (sub_nonneg.mpr (hy i hi)) hpos.le
      have hb1 : b i ≤ 1 := (div_le_one hpos).2 (hbound i hi)
      have hj := (Real.concaveOn_rpow hp hp1).2
        (show u ∈ Set.Ici 0 from hu) (show u + z ∈ Set.Ici 0 from add_nonneg hu hz)
        (sub_nonneg.mpr hb1) hb (show 1 - b i + b i = 1 by ring)
      simp only [smul_eq_mul] at hj
      have hval : (1 - b i) * u + b i * (u + z) = y i := by
        dsimp [b]
        field_simp
        ring
      rw [hval] at hj
      linarith
    have hh := Finset.sum_le_sum hpoint
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.sum_mul, hsum, one_mul] at hh
    linarith

/-- Proposition on the contribution of the removed vertex, for the two
nonempty blocks of the sorted list. Here `s.card = n-r` and `t.card = r-1`. -/
theorem incident_subunit {ι : Type*} (s t : Finset ι) (x y : ι → ℝ) {n : ℕ} {p u : ℝ}
    (hn : n = s.card + t.card + 1) (hs : s.Nonempty) (ht : t.Nonempty)
    (hp : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hy : ∀ j ∈ t, u ≤ y j)
    (hbal : (∑ i ∈ s, x i) + (n : ℝ) * u = ∑ j ∈ t, y j) :
    (∑ i ∈ s, x i ^ p) + (t.card : ℝ) * u ^ p ≤
      (1-1/(n:ℝ)) ^ p * ((∑ i ∈ s, x i^p) + ∑ j ∈ t, y j^p) := by
  let k : ℝ := s.card
  let l : ℝ := t.card
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ s.card from hs.card_pos)
  have hl : 1 ≤ l := by dsimp [l]; exact_mod_cast (show 1 ≤ t.card from ht.card_pos)
  have hn' : (n : ℝ) = k + l + 1 := by dsimp [k,l]; exact_mod_cast hn
  have hd : 0 < k+l := by linarith
  have hnp : 0 < (n : ℝ) := by linarith
  let δ := (1 + 1 / (k+l))^p - 1
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_rpow (by linarith [one_div_pos.mpr hd]) hp.le)
  have hδ' : δ ≤ p/(k+l) := by
    have hB := rpow_one_add_le_one_add_mul_self (p := p)
      (s := 1/(k+l)) (by linarith [one_div_pos.mpr hd]) hp.le hp1.le
    dsimp [δ]
    rw [sub_le_iff_le_add]
    convert hB using 1; ring
  have hmain := reduced_incident s x hs hl hp hp1 hu hx hδ hδ'
  have hlow := concentrate_rpow t y hu hy hp.le hp1.le
  have heq : u + ∑ i ∈ t, (y i - u) = (∑ i ∈ s, x i) + (k+2)*u := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change u + ((∑ i ∈ t, y i) - l*u) = _
    rw [← hbal, hn']
    ring
  rw [heq] at hlow
  have hInv : 1/(1-1/(n:ℝ)) = 1 + 1/(k+l) := by
    rw [hn']; field_simp [ne_of_gt hd, show k+l+1 ≠ 0 by linarith]; ring
  have hI : (1/(1-1/(n:ℝ)))^p = 1+δ := by rw [hInv]; dsimp [δ]; ring
  let T := (∑ i ∈ s, x i^p) + l * u^p
  have hfinal : (1/(1-1/(n:ℝ)))^p*T ≤ (∑ i ∈ s, x i^p) + ∑ j ∈ t, y j^p := by
    rw [hI]
    dsimp [T]
    change _ + (l-1)*u^p ≤ _ at hlow
    change δ * _ + (1+l*δ)*u^p ≤ ((∑ i ∈ s, x i) + (k+2)*u)^p at hmain
    linarith only [hmain, hlow]
  have hc : 0 < 1-1/(n:ℝ) := by apply sub_pos.mpr; exact (div_lt_one hnp).2 (by linarith)
  rw [one_div, Real.inv_rpow hc.le, inv_mul_eq_div] at hfinal
  have haux := (div_le_iff₀ (Real.rpow_pos_of_pos hc p)).mp hfinal
  simpa only [mul_comm ((∑ i ∈ s, x i^p) + ∑ j ∈ t, y j^p)] using haux
end SharpVariation
