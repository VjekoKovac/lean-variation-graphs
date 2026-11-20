module
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The two Hölder coefficients in Section 2 of arXiv:2603.12462v1 -/

namespace SharpVariation
open scoped BigOperators

/-- The distinguished Jensen weight. The lower bound on the number of upper
vertices gives the factor at least three in the weighted argument. -/
private theorem weight_bound {v b p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (hv : 1 - p ≤ v) (hb : 3 ≤ b) :
    v + p ≤ v * (b / v) ^ p := by
  have hb0 : 0 < b := by linarith
  have hlogb : 1 ≤ Real.log b := by
    rw [← Real.exp_le_exp, Real.exp_log hb0]
    exact Real.exp_one_lt_three.le.trans hb
  have hi : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0.ne'
  have hvlog : v - 1 ≤ (1-p) * Real.log v := by
    calc
      v - 1 = v * (1 - v⁻¹) := by rw [mul_sub, mul_one, hi]
      _ ≤ (1-p) * (1 - v⁻¹) := mul_le_mul_of_nonpos_right hv (by
        have : 1 ≤ v⁻¹ := (one_le_inv₀ hv0).2 hv1
        linarith)
      _ ≤ (1-p) * Real.log v :=
        mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hv0) (by linarith)
  calc
    v + p ≤ Real.exp (v + p - 1) := by linarith [Real.add_one_le_exp (v + p - 1)]
    _ ≤ Real.exp ((1-p) * Real.log v + p * Real.log b) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlogb hp.le]
    _ = v * (b / v) ^ p := by
      rw [Real.rpow_def_of_pos (div_pos hb0 hv0), Real.log_div hb0.ne' hv0.ne']
      conv_rhs => lhs; rw [← Real.exp_log hv0]
      rw [← Real.exp_add]
      congr 1
      ring


/-- The dual coefficient budget for the paper's Hölder step. It holds also
when δ is replaced by its larger Bernoulli upper bound p/(k+l). -/
theorem holder_budget {k l δ p : ℝ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ) (hδ' : δ ≤ p/(k+l)) :
    (δ * k^(1-p))^(1/(1-p)) +
      ((1+l*δ)/(k+2)^p)^(1/(1-p)) ≤ 1 := by
  let w := p/(k+l)
  let v := 1-k*w
  have hd : 0 < k+l := by linarith
  have hk0 : 0 < k := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hb : 0 < k+2 := by linarith
  have hpc : 0 < 1-p := by linarith
  have hq : 1 ≤ 1/(1-p) := (one_le_div hpc).mpr (by linarith)
  have hw : 0 < w := div_pos hp hd
  have hw1 : w ≤ 1 := (div_le_one hd).2 (by linarith)
  have hkw : (k+l)*w = p := by dsimp [w]; field_simp
  have hvp : 1-p ≤ v := by dsimp [v]; linarith [mul_nonneg hl0 hw.le]
  have hv : 0 < v := hpc.trans_le hvp
  have hv1 : v ≤ 1 := by dsimp [v]; linarith [mul_nonneg hk0.le hw.le]
  have hraise {z : ℝ} (hz : 0 ≤ z) : (z^(1-p))^(1/(1-p)) = z := by
    rw [← Real.rpow_mul hz, mul_one_div_cancel hpc.ne', Real.rpow_one]
  have hfst : (δ * k^(1-p))^(1/(1-p)) ≤ k*w := by
    rw [Real.mul_rpow hδ (Real.rpow_nonneg hk0.le _), hraise hk0.le, mul_comm]
    apply mul_le_mul_of_nonneg_left _ hk0.le
    exact (Real.rpow_le_self_of_le_one hδ (hδ'.trans hw1) hq).trans hδ'
  have hcost := weight_bound hp hp1 hv hv1 hvp (show 3 ≤ k+2 by linarith)
  have hraw : 1+l*δ ≤ v*((k+2)/v)^p := by
    dsimp [v] at hcost ⊢
    linarith [mul_le_mul_of_nonneg_left hδ' hl0]
  have hcon : (1+l*δ)/(k+2)^p ≤ v^(1-p) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hb p)).mpr
    rw [Real.div_rpow hb.le hv.le] at hraw
    rw [Real.rpow_sub hv, Real.rpow_one]
    apply hraw.trans_eq
    ring
  have hsnd : ((1+l*δ)/(k+2)^p)^(1/(1-p)) ≤ v := by
    rw [← hraise hv.le]
    exact Real.rpow_le_rpow (by positivity) hcon (by positivity)
  dsimp [v] at hsnd
  linarith

/-- The paper's function φ(x), expressed as the sum of the powers of s and t
before expanding their factors. This covers the whole real interval [2,n-1]. -/
theorem paper_coefficients_le_one {n x p : ℝ} (hx : 2 ≤ x) (hxn : x ≤ n-1)
    (hp : 0 < p) (hp1 : p < 1) :
    let δ := (n/(n-1))^p - 1
    (δ*(n-x)^(1-p))^(1/(1-p)) + ((1+(x-1)*δ)/(n-x+2)^p)^(1/(1-p)) ≤ 1 := by
  have hn : 0 < n-1 := by linarith
  have he : n/(n-1) = 1+1/(n-1) := by field_simp; ring
  apply holder_budget (by linarith) (by linarith) hp hp1
  · apply sub_nonneg.mpr
    exact Real.one_le_rpow ((one_le_div hn).mpr (by linarith)) hp.le
  · rw [he, show n-x + (x-1) = n-1 by ring]
    have h := rpow_one_add_le_one_add_mul_self (s := 1/(n-1)) (p := p)
      (by linarith [one_div_pos.mpr hn]) hp.le hp1.le
    rw [sub_le_iff_le_add]
    convert h using 1; ring

/-- The expanded expression for φ in the source, on the entire real interval. -/
theorem paper_phi_le_one {n x p : ℝ} (hx : 2 ≤ x) (hxn : x ≤ n-1)
    (hp : 0 < p) (hp1 : p < 1) :
    ((n/(n-1))^p-1)^(1/(1-p))*(n-x) +
      ((n/(n-1))^p*(x-1)-x+2)^(1/(1-p))*(n-x+2)^(-p/(1-p)) ≤ 1 := by
  let δ := (n/(n-1))^p-1
  have hn : 0 < n-1 := by linarith
  have hk : 0 ≤ n-x := by linarith
  have hb : 0 < n-x+2 := by linarith
  have hl : 0 ≤ x-1 := by linarith
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_rpow ((one_le_div hn).mpr (by linarith)) hp.le)
  have hpc : 0 < 1-p := by linarith
  have h := paper_coefficients_le_one hx hxn hp hp1
  change (δ * (n-x)^(1-p))^(1/(1-p)) + ((1+(x-1)*δ)/(n-x+2)^p)^(1/(1-p)) ≤ 1 at h
  rw [Real.mul_rpow hδ (Real.rpow_nonneg hk _), ← Real.rpow_mul hk, mul_one_div_cancel hpc.ne',
    Real.rpow_one, Real.div_rpow (by positivity : 0 ≤ 1+(x-1)*δ) (Real.rpow_nonneg hb.le _),
    ← Real.rpow_mul hb.le] at h
  have he : 1+(x-1)*δ = (n/(n-1))^p*(x-1)-x+2 := by dsimp [δ]; ring
  rw [he] at h
  rw [show -p/(1-p) = -(p*(1/(1-p))) by ring, Real.rpow_neg hb.le]
  simpa only [δ, div_eq_mul_inv] using h

/-- Two-term Hölder with exponents 1/p and 1/(1-p), including vanishing entries. -/
theorem holder_two {a b s t p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hp : 0 < p) (hp1 : p < 1) (h : s^(1/(1-p)) + t^(1/(1-p)) ≤ 1) :
    a^p*s + b^p*t ≤ (a+b)^p := by
  let f (i : Bool) : ℝ := if i then a^p else b^p
  let g (i : Bool) : ℝ := if i then s else t
  have hpc : 0 < 1-p := by linarith
  have hc : Real.HolderConjugate (1/p) (1/(1-p)) :=
    ⟨by simp [one_div], one_div_pos.mpr hp, one_div_pos.mpr hpc⟩
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset Bool))
    (f := f) (g := g) hc
    (by intro i _; cases i <;> simp [f] <;> positivity)
    (by intro i _; cases i <;> simp [g,hs,ht])
  have hnorm (z : ℝ) (hz : 0 ≤ z) : (z^p)^(1/p) = z := by
    rw [← Real.rpow_mul hz, mul_one_div_cancel hp.ne', Real.rpow_one]
  simp only [Fintype.sum_bool, f, g, Bool.false_eq_true, ↓reduceIte, hnorm a ha, hnorm b hb,
    one_div_one_div] at hh
  have hle : (s^(1/(1-p)) + t^(1/(1-p)))^(1-p) ≤ 1 :=
    Real.rpow_le_one (by positivity) h hpc.le
  exact hh.trans (mul_le_of_le_one_right (Real.rpow_nonneg (add_nonneg ha hb) _) hle)

/-- Uniform Jensen for x, the paper's s,t substitution, and two-term Hölder. -/
theorem reduced_incident {ι : Type*} (q : Finset ι) (x : ι → ℝ) {l δ p u : ℝ}
    (hq : q.Nonempty) (hl : 1 ≤ l) (hp : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u)
    (hx : ∀ i ∈ q, 0 ≤ x i) (hδ : 0 ≤ δ) (hδ' : δ ≤ p/((q.card:ℝ)+l)) :
    δ*(∑ i ∈ q, x i^p) + (1+l*δ)*u^p ≤ ((∑ i ∈ q, x i) + ((q.card:ℝ)+2)*u)^p := by
  let k : ℝ := q.card
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ q.card from hq.card_pos)
  have hk0 : 0 < k := by linarith
  have hb : 0 < k+2 := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hX := Finset.sum_nonneg hx
  let X := ∑ i ∈ q, x i
  have hj := (Real.concaveOn_rpow hp.le hp1.le).le_map_sum (t := q) (w := fun _ => k⁻¹)
    (p := x) (fun _ _ => inv_nonneg.mpr hk0.le)
    (by simp [k, show (q.card:ℝ) ≠ 0 from hk0.ne'])
    (fun i hi => Set.mem_Ici.mpr (hx i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum, Real.mul_rpow (inv_nonneg.mpr hk0.le) hX,
    Real.inv_rpow hk0.le] at hj
  have hJ : (∑ i ∈ q, x i^p) ≤ k^(1-p)*X^p := by
    rw [Real.rpow_sub hk0, Real.rpow_one]
    change k⁻¹ * _ ≤ _ * X^p at hj
    rw [inv_mul_eq_div, div_le_iff₀ hk0] at hj
    apply hj.trans_eq
    ring
  have hbudget := holder_budget hk hl hp hp1 hδ hδ'
  have h := holder_two (a := X) (b := (k+2)*u) hX (by positivity)
    (s := δ*k^(1-p)) (t := (1+l*δ)/(k+2)^p) (by positivity) (by positivity) hp hp1 hbudget
  rw [Real.mul_rpow hb.le hu] at h
  have hcancel : (k+2)^p * u^p * ((1+l*δ)/(k+2)^p) = (1+l*δ)*u^p := by
    field_simp
  rw [hcancel] at h
  change _ ≤ (X + (k+2)*u)^p
  linarith [mul_le_mul_of_nonneg_left hJ hδ]

end SharpVariation
