module
public import SharpVariation.Analytic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

@[expose] public section

/-! # Complete-graph variational estimates

The convex-exponent argument follows González-Riquelme and Madrid,
arXiv:2005.03146, proof of Theorem 1(i), cited in §2 of arXiv:2603.12462.
The deletion step in the concave range uses the least value above the mean,
as in the latter paper.
-/
namespace SharpVariation
namespace CompleteGraph

open Finset
variable {ι : Type*}

noncomputable def mean (s : Finset ι) (f : ι → ℝ) : ℝ := (∑ i ∈ s, f i) / s.card

noncomputable def energy (s : Finset ι) (p : ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, |f i - f j| ^ p

private noncomputable def directed (p : ℝ) (a b : ℝ) := max (a-b) 0 ^ p

private theorem energy_eq_directed (s : Finset ι) {p : ℝ} (hp : 0 < p) (f : ι → ℝ) :
    energy s p f = 2 * ∑ i ∈ s, ∑ j ∈ s, directed p (f i) (f j) := by
  have split (a b : ℝ) : |a-b|^p = directed p a b + directed p b a := by
    unfold directed
    rcases le_total a b with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), Real.zero_rpow hp.ne',
        zero_add, abs_of_nonpos (by linarith), neg_sub]
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), Real.zero_rpow hp.ne',
        add_zero, abs_of_nonneg (by linarith)]
  simp_rw [energy, split, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => directed p (f j) (f i))]
  ring

/-- Uniform Jensen on the row with its diagonal entry omitted. -/
private theorem convex_row [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (i : ι)
    (hi : i ∈ s) (hs : 2 ≤ s.card) {p : ℝ} (hp : 1 ≤ p) :
    ∑ j ∈ s, directed p (max (f i) (mean s f)) (max (f j) (mean s f)) ≤
      (1 - 1 / (s.card : ℝ)) ^ p * ∑ j ∈ s, directed p (f i) (f j) := by
  let t := s.erase i
  let d := fun j => max (f i - f j) 0
  have hp0 : 0 < p := by linarith
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast (by omega : 0 < s.card)
  have htc : (t.card : ℝ) = s.card - 1 := by
    dsimp [t]; rw [Finset.card_erase_of_mem hi, Nat.cast_sub (by omega : 1 ≤ s.card)]; norm_num
  have h2 : (2:ℝ) ≤ s.card := by exact_mod_cast hs
  have ht : 0 < (t.card : ℝ) := by rw [htc]; linarith
  have hr : 0 ≤ (1 - 1 / (s.card : ℝ)) := by rw [sub_nonneg, div_le_one hn]; linarith
  have hc : (t.card : ℝ) / s.card = 1 - 1 / (s.card : ℝ) := by rw [htc]; field_simp
  have hmean : f i - mean s f ≤ (∑ j ∈ t, d j) / s.card := by
    rw [mean, sub_div' hn.ne']
    apply (div_le_div_iff_of_pos_right hn).2
    calc (f i) * s.card - ∑ j ∈ s, f j = ∑ j ∈ s, (f i - f j) := by
            simp [Finset.sum_sub_distrib, mul_comm]
         _ ≤ ∑ j ∈ s, d j := Finset.sum_le_sum fun j _ => le_max_left _ _
         _ = ∑ j ∈ t, d j := by rw [← Finset.sum_erase_add _ _ hi]; simp [d, t]
  have htotal : 0 ≤ ∑ j ∈ t, d j := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hb (j : ι) : max (max (f i) (mean s f) - max (f j) (mean s f)) 0 ≤
      (∑ k ∈ t, d k) / s.card := by
    apply max_le _ (div_nonneg htotal hn.le)
    have h := le_max_right (f j) (mean s f)
    rcases le_total (f i) (mean s f) with h' | h'
    · rw [max_eq_right h']; linarith [div_nonneg htotal hn.le]
    · rw [max_eq_left h']; linarith
  have hj := Real.rpow_arith_mean_le_arith_mean_rpow t (fun _ => (t.card : ℝ)⁻¹) d
    (fun _ _ => inv_nonneg.mpr ht.le) (by simp [ht.ne']) (fun j _ => le_max_right _ _) hp
  simp only [← Finset.mul_sum] at hj
  have hsum (g : ι → ℝ) :
      ∑ j ∈ s, directed p (g i) (g j) = ∑ j ∈ t, directed p (g i) (g j) := by
    rw [← Finset.sum_erase_add _ _ hi]; simp [directed, t, hp0.ne']
  rw [hsum (fun j => max (f j) (mean s f)), hsum f]
  calc
    _ ≤ ∑ _j ∈ t, ((∑ k ∈ t, d k) / s.card) ^ p :=
      Finset.sum_le_sum fun j _ => Real.rpow_le_rpow (le_max_right _ _) (hb j) hp0.le
    _ = (t.card : ℝ) * (1 - 1 / (s.card : ℝ)) ^ p *
          ((t.card : ℝ)⁻¹ * ∑ k ∈ t, d k) ^ p := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, ← Real.mul_rpow hr (mul_nonneg (inv_nonneg.mpr ht.le) htotal)]
      congr 2
      rw [← hc]; field_simp
    _ ≤ (t.card : ℝ) * (1 - 1 / (s.card : ℝ)) ^ p *
          ((t.card : ℝ)⁻¹ * ∑ j ∈ t, d j ^ p) :=
      mul_le_mul_of_nonneg_left hj (mul_nonneg ht.le (Real.rpow_nonneg hr _))
    _ = _ := by dsimp [directed, d]; field_simp

/-- The sharp bound for all convex exponents, expressed using ordered pairs. -/
theorem energy_above_one (s : Finset ι) (f : ι → ℝ) (hs : 2 ≤ s.card) {p : ℝ} (hp : 1 ≤ p) :
    energy s p (fun i => max (f i) (mean s f)) ≤
      (1 - 1 / (s.card : ℝ)) ^ p * energy s p f := by
  classical
  have hp0 : 0 < p := by linarith
  rw [energy_eq_directed s hp0, energy_eq_directed s hp0, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => convex_row s f i hi hs hp


/-- Partition the ordered-pair energy into the smaller graph and two copies of
the deleted vertex's incident row. -/
theorem energy_delete [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 < p) {a : ι} (ha : a ∈ s) :
    energy s p f = energy (s.erase a) p f + 2 * ∑ i ∈ s.erase a, |f i - f a| ^ p := by
  have hi : a ∉ s.erase a := Finset.notMem_erase _ _
  conv_lhs => rw [← Finset.insert_erase ha]
  unfold energy
  simp only [Finset.sum_insert hi, sub_self, abs_zero, Real.zero_rpow hp.ne', zero_add,
    Finset.sum_add_distrib]
  simp_rw [abs_sub_comm (f a)]
  ring

private theorem energy_nonneg (s : Finset ι) (f : ι → ℝ) (p : ℝ) : 0 ≤ energy s p f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

private theorem energy_threshold_mono (s : Finset ι) (f : ι → ℝ) {p l m : ℝ}
    (hp : 0 ≤ p) (h : l ≤ m) : energy s p (fun i => max (f i) m) ≤
      energy s p (fun i => max (f i) l) := by
  have hm (x : ℝ) : max (max x l) m = max x m := by rw [max_assoc, max_eq_right h]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Real.rpow_le_rpow (abs_nonneg _) _ hp
  simpa only [hm] using abs_max_sub_max_le_abs (max (f i) l) (max (f j) l) m

private theorem mean_delete_le [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) {a : ι}
    (ha : a ∈ s) (hs : 2 ≤ s.card) (hm : mean s f ≤ f a) :
    mean (s.erase a) f ≤ mean s f := by
  have he : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  have hr : ((s.erase a).card : ℝ) = s.card - 1 := by rw [he, Nat.cast_sub (by omega : 1 ≤ s.card)]; simp
  have hn : 0 < ((s.erase a).card : ℝ) := by exact_mod_cast (by omega : 0 < (s.erase a).card)
  have hn' : (s.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  have hb : mean s f * s.card = ∑ i ∈ s, f i := by simp [mean, hn']
  have hsum := Finset.sum_erase_add s f ha
  change (∑ i ∈ s.erase a, f i) / _ ≤ _
  rw [div_le_iff₀ hn, hr]
  linarith

/-- If only the pivot lies strictly above the mean, bound the original
energy using the stars of a largest and a smallest value (GRM, Lemma 10). -/
private theorem solitary_high [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {a : ι} (ha : a ∈ s)
    (hs : 2 ≤ s.card) (ham : mean s f ≤ f a)
    (hlo : ∀ i ∈ s.erase a, f i ≤ mean s f) :
    energy s p (fun i => max (f i) (mean s f)) ≤
      (1 - 1 / (s.card : ℝ)) ^ p * energy s p f := by
  let t := s.erase a
  let m := mean s f
  let g := fun i => max (f i) m
  have htc : t.card = s.card - 1 := Finset.card_erase_of_mem ha
  have ht : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hmin⟩ := t.exists_min_image f ht
  have htc' : (t.card : ℝ) = s.card - 1 := by rw [htc, Nat.cast_sub (by omega : 1 ≤ s.card)]; simp
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast (by omega : 0 < s.card)
  have h1 : 1 ≤ (s.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ s.card)
  have hc : 0 ≤ 1 - 1 / (s.card : ℝ) := by rw [sub_nonneg, div_le_iff₀ hn, one_mul]; exact h1
  have hm : f a - m ≤ (1 - 1 / (s.card : ℝ)) * (f a - f b) := by
    have hh := Finset.sum_le_sum (s := t) (fun i hi => hmin i hi)
    have hsum := Finset.sum_erase_add s f ha
    simp only [Finset.sum_const, nsmul_eq_mul, htc'] at hh
    change f a - (∑ i ∈ s, f i) / (s.card : ℝ) ≤ _
    field_simp
    dsimp [t] at hh
    nlinarith
  have hd : 0 ≤ f a - f b := by linarith [hlo b hb]
  have hpow := Real.rpow_le_rpow (sub_nonneg.mpr ham) hm hp.le
  rw [Real.mul_rpow hc hd] at hpow
  have hg (i : ι) (hi : i ∈ t) : g i = m := max_eq_right (hlo i hi)
  have hga : g a = f a := max_eq_left ham
  have he0 : energy t p g = 0 := by
    unfold energy
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simp [hg i hi, hg j hj, hp.ne']
  have hstar : ∑ i ∈ t, |g i - g a| ^ p = t.card * (f a - m) ^ p := by
    calc _ = ∑ _i ∈ t, (f a-m)^p := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hg i hi, hga, abs_of_nonpos (by linarith : m - f a ≤ 0), neg_sub]
         _ = _ := by simp
  have hab : ∀ i ∈ t, (f a - f b) ^ p ≤ |f i - f a| ^ p + |f i - f b| ^ p := by
    intro i hi
    have hai : f i ≤ f a := (hlo i hi).trans ham
    rw [abs_sub_comm (f i) (f a), abs_of_nonneg (sub_nonneg.mpr hai),
      abs_of_nonneg (sub_nonneg.mpr (hmin i hi))]
    simpa only [sub_add_sub_cancel] using
      (Real.rpow_add_le_add_rpow (sub_nonneg.mpr hai) (sub_nonneg.mpr (hmin i hi)) hp.le hp1)
  have hdiam := Finset.sum_le_sum hab
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at hdiam
  have hstarb : ∑ i ∈ t, |f i - f b| ^ p = ∑ i ∈ t.erase b, |f i - f b| ^ p := by
    rw [← Finset.sum_erase_add t (fun i => |f i - f b| ^ p) hb]
    simp [hp.ne']
  rw [hstarb] at hdiam
  have hlow := energy_nonneg (t.erase b) f p
  have hlow' := energy_delete t f hp hb
  have hglobal := energy_delete s f hp ha
  change energy s p g ≤ _
  rw [energy_delete s g hp ha]
  change energy t p g + 2 * (∑ i ∈ t, |g i-g a|^p) ≤ _
  rw [he0, hstar, zero_add]
  have hpre : 2 * ((t.card : ℝ) * (f a - f b)^p) ≤ energy s p f := by
    change energy s p f = energy t p f + 2 * ∑ i ∈ t, |f i-f a|^p at hglobal
    linarith
  calc
    _ ≤ 2 * (t.card * ((1 - 1 / (s.card : ℝ)) ^ p * (f a - f b) ^ p)) := by gcongr
    _ = (1 - 1 / (s.card : ℝ)) ^ p * (2 * (t.card * (f a - f b) ^ p)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpre (Real.rpow_nonneg hc _)


/-- Induction on the vertex set in §2, including the extremal single-high case. -/
theorem energy_below_one (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    energy s p (fun i => max (f i) (mean s f)) ≤
      (1 - 1 / (s.card : ℝ)) ^ p * energy s p f := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : 2 ≤ s.card
    · let m := mean s f
      let above := s.filter fun i => m < f i
      by_cases hab : above.Nonempty
      · obtain ⟨a, ha, hmin⟩ := above.exists_min_image f hab
        have has := (Finset.mem_filter.mp ha).1
        have ham : m < f a := (Finset.mem_filter.mp ha).2
        let t := s.erase a
        let l := t.filter fun i => f i ≤ m
        let h := t \ l
        have hlsub : l ⊆ t := Finset.filter_subset _ _
        have hlval {i} (hi : i ∈ l) : f i ≤ m := (Finset.mem_filter.mp hi).2
        have hhval {i} (hi : i ∈ h) : f a ≤ f i := by
          obtain ⟨hit, hil⟩ := Finset.mem_sdiff.mp hi
          have him : m < f i := lt_of_not_ge fun him => hil (Finset.mem_filter.mpr ⟨hit, him⟩)
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hit, him⟩)
        have hcardt : t.card = s.card - 1 := Finset.card_erase_of_mem has
        have hcard : s.card = h.card + l.card + 1 := by
          have := Finset.card_sdiff_add_card_eq_card hlsub
          change h.card + l.card = t.card at this
          omega
        have hmean : (s.card : ℝ) * m = ∑ i ∈ s, f i := by
          dsimp [m, mean]
          have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
          field_simp
        have constsum (z : ℝ) : (∑ _i ∈ s, z) = (s.card : ℝ) * z := by simp
        have hlne : l.Nonempty := by
          by_contra! he
          have hall : ∀ i ∈ s, m < f i := by
            intro i hi
            by_cases heq : i = a
            · simpa [heq] using ham
            · exact lt_of_not_ge fun hle =>
                (Finset.notMem_empty i) (he ▸ (Finset.mem_filter.mpr
                  ⟨Finset.mem_erase.mpr ⟨heq, hi⟩, hle⟩ : i ∈ l))
          have := Finset.sum_lt_sum_of_nonempty (show s.Nonempty from ⟨a, has⟩) hall
          rw [constsum, hmean] at this
          exact (lt_irrefl _ this)
        by_cases hh : h.Nonempty
        · have hsplit (F : ι → ℝ) : (∑ i ∈ h, F i) + (∑ i ∈ l, F i) = ∑ i ∈ t, F i :=
            Finset.sum_sdiff hlsub
          have hce : (h.card : ℝ) + l.card + 1 = s.card := by exact_mod_cast hcard.symm
          have htsum : (∑ i ∈ t, f i) + f a = ∑ i ∈ s, f i := Finset.sum_erase_add s f has
          have hbal :
              (∑ i ∈ h, (f i - f a)) + (s.card : ℝ) * (f a - m) = ∑ j ∈ l, (f a - f j) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
            have hz := congrArg (fun z : ℝ => z * f a) hce
            linarith [hsplit f]
          have hstep := incident_subunit h l (fun i => f i - f a) (fun i => f a - f i)
            hcard hh hlne hp hp1 (sub_nonneg.mpr ham.le) (fun _ hi => sub_nonneg.mpr (hhval hi))
            (fun _ hi => sub_le_sub_left (hlval hi) _) hbal
          let g := fun i => max (f i) m
          have hr1 : (∑ i ∈ t, |g i - g a| ^ p) =
              (∑ i ∈ h, (f i - f a) ^ p) + (l.card : ℝ) * (f a - m) ^ p := by
            rw [← hsplit]
            congr 1
            · apply Finset.sum_congr rfl
              intro i hi
              rw [show g i = f i from max_eq_left (ham.le.trans (hhval hi)),
                show g a = f a from max_eq_left ham.le, abs_of_nonneg (sub_nonneg.mpr (hhval hi))]
            · calc _ = ∑ _i ∈ l, (f a-m)^p := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [show g i = m from max_eq_right (hlval hi),
                          show g a = f a from max_eq_left ham.le, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ham.le)]
                   _ = _ := by simp
          have hr2 : (∑ i ∈ t, |f i - f a| ^ p) =
              (∑ i ∈ h, (f i - f a) ^ p) + ∑ i ∈ l, (f a - f i)^p := by
            rw [← hsplit]
            congr 1
            · exact Finset.sum_congr rfl fun i hi => by rw [abs_of_nonneg (sub_nonneg.mpr (hhval hi))]
            · exact Finset.sum_congr rfl fun i hi => by
                rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ((hlval hi).trans ham.le))]
          rw [← hr1, ← hr2] at hstep
          have hiht := ih t (Finset.erase_ssubset has)
          have hprev := energy_threshold_mono t f hp.le (mean_delete_le s f has hs ham.le)
          have htc0 : 0 < (t.card : ℝ) := by exact_mod_cast (by omega : 0 < t.card)
          have htc1 : 1 ≤ (t.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ t.card)
          have hcs : (t.card : ℝ) ≤ s.card := by exact_mod_cast (by omega : t.card ≤ s.card)
          have hnon : 0 ≤ 1 - 1 / (t.card : ℝ) := by rw [sub_nonneg, div_le_one htc0]; exact htc1
          have hmul := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hnon (sub_le_sub_left (one_div_le_one_div_of_le htc0 hcs) _) hp.le)
            (energy_nonneg t f p)
          have hsmall : energy t p g ≤ (1 - 1 / (s.card : ℝ)) ^ p * energy t p f :=
            hprev.trans (hiht.trans hmul)
          change energy s p g ≤ _
          rw [energy_delete s g hp has, energy_delete s f hp has]
          change energy t p g + 2 * (∑ i ∈ t, |g i-g a|^p) ≤ _ *
            (energy t p f + 2 * ∑ i ∈ t, |f i-f a|^p)
          linarith
        · apply solitary_high s f hp hp1.le has hs ham.le
          intro i hi
          by_contra! hgt
          exact hh ⟨i, Finset.mem_sdiff.mpr ⟨hi, fun hil => (not_lt_of_ge (hlval hil)) hgt⟩⟩
      · have hm (i : ι) (hi : i ∈ s) : max (f i) m = m :=
          max_eq_right (le_of_not_gt fun h => hab ⟨i, Finset.mem_filter.mpr ⟨hi,h⟩⟩)
        have hz : energy s p (fun i => max (f i) m) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          apply Finset.sum_eq_zero
          intro j hj
          simp [hm i hi, hm j hj, hp.ne']
        rw [show energy s p (fun i => max (f i) (mean s f)) = 0 from hz]
        have h1 : (1:ℝ) ≤ s.card := by exact_mod_cast (by omega : 1 ≤ s.card)
        apply mul_nonneg _ (energy_nonneg s f p)
        apply Real.rpow_nonneg
        rw [sub_nonneg, div_le_one (by linarith : 0 < (s.card : ℝ))]
        exact h1
    · have hsmall : s.card ≤ 1 := by omega
      have hz (g : ι → ℝ) : energy s p g = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.card_le_one_iff.mp hsmall hi hj]
        simp [hp.ne']
      rw [hz, hz, mul_zero]

end CompleteGraph

/-- The sharp ordered-pair inequality at every positive exponent. -/
theorem complete_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hs : 2 ≤ s.card)
    {p : ℝ} (hp : 0 < p) :
    CompleteGraph.energy s p (fun i => max (f i) (CompleteGraph.mean s f)) ≤
      (1 - 1 / (s.card : ℝ)) ^ p * CompleteGraph.energy s p f := by
  rcases lt_or_ge p 1 with h | h
  · exact CompleteGraph.energy_below_one s f hp h
  · exact CompleteGraph.energy_above_one s f hs h

end SharpVariation
