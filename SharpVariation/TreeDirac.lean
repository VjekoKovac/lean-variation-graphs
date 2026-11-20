module
public import SharpVariation.Graph
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

/-! # Root point mass and parallel edges in the branching tree

These lemmas isolate the counting-to-variation step of §5 of
González-Riquelme–Kovač–Madrid, arXiv:2603.12462.
-/

open Finset
namespace SharpVariation.TreeExample

variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

/-- The function supported at the root, with value one there. -/
def dirac (v : V) (x : V) : ℝ := by
  classical
  exact if x = v then 1 else 0

private theorem average_dirac (v x : V) (r : ℕ) : ballAverage G (dirac v) x r =
    (if G.dist x v ≤ r then 1 else 0) / (closedBall G x r).card := by
  classical
  simp [ballAverage, dirac, abs_ite, mem_closedBall]

/-- The smallest ball containing the root attains the maximal average. -/
theorem maximal_dirac (hc : G.Connected) (v x : V) : maximal G (dirac v) x =
    1 / ((closedBall G x (G.dist x v)).card : ℝ) := by
  classical
  have ht : 0 < ((closedBall G x (G.dist x v)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨v, mem_closedBall.mpr le_rfl⟩
  apply le_antisymm
  · apply sup'_le
    intro r _
    rw [average_dirac]
    split_ifs with h
    · apply one_div_le_one_div_of_le ht
      exact_mod_cast card_le_card (show closedBall G x (G.dist x v) ⊆ closedBall G x r
        from fun _ hy => mem_closedBall.mpr ((mem_closedBall.mp hy).trans h))
    · simp [ht.le]
  · have h := ballAverage_le_maximal hc (dirac v) x (G.dist x v)
    simpa only [average_dirac, le_refl, ite_true] using h

/-- A point mass on a vertex of degree one has unit variation for every
positive exponent. -/
theorem variation_dirac_degree_one (v a : V) (ha : ∀ z, G.Adj v z ↔ z = a)
    (p : ℝ) (hp : 0 < p) : variation G p (dirac v) = 1 := by
  classical
  have hne : v ≠ a := fun h => G.loopless.irrefl v ((ha v).mpr h)
  have hterm (i j : V) :
      (if G.Adj i j then |dirac v i - dirac v j|^p else 0) =
        (if i = v then (if j = a then 1 else 0) else 0) +
        (if i = a then (if j = v then 1 else 0) else 0) := by
    by_cases hi : i = v <;> by_cases hj : j = v
    · subst i; subst j; simp [hne]
    · subst i; simp [dirac, hj, hne, ha]
    · subst j; rw [G.adj_comm]; simp [dirac, hi, ha]
    · simp [dirac, hi, hj, Real.zero_rpow hp.ne']
  unfold variation energy
  simp_rw [hterm, Finset.sum_add_distrib]
  simp [Finset.sum_ite_irrel]

private theorem count_edges (p : ℝ) (hp : 0 < p) (g : V → ℝ) (b w : I → V)
    (hb : Function.Injective b) (hw : Function.Injective w)
    (hd : ∀ i j, b i ≠ w j) (ha : ∀ i, G.Adj (b i) (w i))
    {d : ℝ} (hd0 : 0 ≤ d) (hg : ∀ i, d ≤ g (b i) - g (w i)) :
    (Fintype.card I : ℝ)*d^p ≤ energy G p g := by
  classical
  let e (u v : V) := if G.Adj u v then |g u - g v| ^ p else 0
  let R (u : V) := ∑ v, e u v
  have he (u v : V) : 0 ≤ e u v := by dsimp [e]; split <;> positivity
  have hR (u : V) : 0 ≤ R u := Finset.sum_nonneg fun i _ => he u i
  have hrow (u v : V) : e u v ≤ R u :=
    Finset.single_le_sum (fun z _ => he u z) (Finset.mem_univ v)
  have hed (i : I) : d^p ≤ |g (b i) - g (w i)|^p :=
    Real.rpow_le_rpow hd0 ((hg i).trans (le_abs_self _)) hp.le
  have hbrow (i : I) : d^p ≤ R (b i) :=
    (show d^p ≤ e (b i) (w i) by simpa [e, ha] using hed i).trans (hrow _ _)
  have hwrow (i : I) : d^p ≤ R (w i) :=
    (show d^p ≤ e (w i) (b i) by
      simpa [e, (ha i).symm, abs_sub_comm (g (w i))] using hed i).trans (hrow _ _)
  have hdj : Disjoint (univ.image b) (univ.image w) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv'
    exact hd i j hj.symm
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (s := univ.image b ∪ univ.image w) (t := univ) (f := R)
    (subset_univ _) (fun i _ _ => hR i)
  rw [Finset.sum_union hdj, Finset.sum_image hb.injOn, Finset.sum_image hw.injOn] at hsum
  have h1 := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hbrow i)
  have h2 := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hwrow i)
  simp only [sum_const, card_univ, nsmul_eq_mul] at h1 h2
  change _ ≤ (∑ i, R i)/2
  linarith

/-- The geometric inputs are exactly the two ball counts, the root's sole
neighbor and the family of distinct parallel edges. -/
theorem tree_dirac_energy (hc : G.Connected) (v a : V) (b w : I → V)
    (hroot : ∀ z, G.Adj v z ↔ z = a)
    (hb : Function.Injective b) (hw : Function.Injective w)
    (hd : ∀ i j, b i ≠ w j) (ha : ∀ i, G.Adj (b i) (w i))
    {B D : ℕ} (hB : 0 < B) (hBD : B ≤ D)
    (hsmall : ∀ i, (closedBall G (b i) (G.dist (b i) v)).card ≤ B)
    (hlarge : ∀ i, D ≤ (closedBall G (w i) (G.dist (w i) v)).card)
    (p : ℝ) (hp : 0 < p) :
    variation G p (dirac v) = 1 ∧
      (Fintype.card I : ℝ) * (1 / (B:ℝ) - 1 / (D:ℝ))^p ≤ energy G p (maximal G (dirac v)) := by
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  have hBD' : (B : ℝ) ≤ D := by exact_mod_cast hBD
  refine ⟨variation_dirac_degree_one v a hroot p hp,
    count_edges p hp _ b w hb hw hd ha ?_ ?_⟩
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hB' hBD')
  · intro i
    rw [maximal_dirac hc, maximal_dirac hc]
    apply sub_le_sub
    · apply one_div_le_one_div_of_le
      · exact_mod_cast Finset.card_pos.mpr ⟨v, mem_closedBall.mpr le_rfl⟩
      · exact_mod_cast hsmall i
    · apply one_div_le_one_div_of_le (hB'.trans_le hBD')
      exact_mod_cast hlarge i

end SharpVariation.TreeExample
