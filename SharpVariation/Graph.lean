module

public import SharpVariation.Defs
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
open Finset
namespace SharpVariation
variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

@[simp] theorem mem_closedBall {v w : V} {r : ℕ} :
    w ∈ closedBall G v r ↔ G.dist v w ≤ r := by classical simp [closedBall]

/-- Justifies the finite list of candidate radii in the definition of the operator. -/
theorem ballAverage_le_maximal (hc : G.Connected) (f : V → ℝ) (v : V) (r : ℕ) :
    ballAverage G f v r ≤ maximal G f v := by
  have hr : ∀ (i : ℕ), i ≤ Fintype.card V → ballAverage G f v i ≤ maximal G f v :=
    fun i hi => le_sup' _ (mem_range.mpr (Nat.lt_succ_of_le hi))
  by_cases h : r ≤ Fintype.card V
  · exact hr r h
  have all_ball (i : ℕ) (hi : Fintype.card V ≤ i) : closedBall G v i = univ := by
    ext w
    obtain ⟨t, ht, hlen⟩ := hc.exists_path_of_dist v w
    simp [hlen ▸ ht.length_lt.le.trans hi]
  have heq : ballAverage G f v r = ballAverage G f v (Fintype.card V) := by
    simp [ballAverage, all_ball r (by omega), all_ball _ le_rfl]
  exact heq ▸ hr _ le_rfl

theorem energy_nonneg (G : SimpleGraph V) (p : ℝ) (f : V → ℝ) : 0 ≤ energy G p f := by
  classical
  unfold energy
  exact div_nonneg (sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> positivity) (by norm_num)

theorem energy_abs_le (G : SimpleGraph V) (p : ℝ) (hp : 0 ≤ p) (f : V → ℝ) :
    energy G p (fun i => |f i|) ≤ energy G p f := by
  classical
  unfold energy
  gcongr with i hi j hj
  split_ifs
  · exact Real.rpow_le_rpow (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _) hp
  · rfl

/-- Pass from the edge sum estimate to its p-th root (also for 0 < p < 1). -/
theorem variation_le_of_energy_le {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    {f g : V → ℝ} (h : energy G p g ≤ c ^ p * energy G p f) :
    variation G p g ≤ c * variation G p f := by
  unfold variation
  calc
    _ ≤ (c ^ p * energy G p f) ^ (1 / p) :=
      Real.rpow_le_rpow (energy_nonneg ..) h (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hc _) (energy_nonneg ..), ← Real.rpow_mul hc]
      have hx : p * (1 / p) = 1 := by field_simp
      rw [hx, Real.rpow_one]

private theorem hom_dist_le {A B : Type*} {K : SimpleGraph A} {L : SimpleGraph B} (k : K →g L)
    {a b : A} (h : K.Reachable a b) : L.dist (k a) (k b) ≤ K.dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  simpa [hp] using (SimpleGraph.dist_le (p.map k))

omit [Fintype V] [Fintype W] in
theorem iso_dist (e : G ≃g H) (hc : G.Connected) (v w : V) :
    H.dist (e v) (e w) = G.dist v w := by
  apply le_antisymm (hom_dist_le e.toRelEmbedding.toRelHom (hc v w))
  simpa using hom_dist_le e.symm.toRelEmbedding.toRelHom (e.connected_iff.mp hc (e v) (e w))

theorem iso_ballAverage (e : G ≃g H) (hc : G.Connected) (f : W → ℝ) (v : V) (r : ℕ) :
    ballAverage G (f ∘ e) v r = ballAverage H f (e v) r := by
  classical
  have h : (closedBall G v r).map e.toEquiv.toEmbedding = closedBall H (e v) r := by
    ext a
    obtain ⟨w, rfl⟩ := e.surjective a
    rw [Finset.mem_map_equiv]
    change e.toEquiv.symm (e.toEquiv w) ∈ _ ↔ _
    rw [Equiv.symm_apply_apply, mem_closedBall, mem_closedBall, iso_dist e hc]
  simp [ballAverage, ← h]

theorem iso_maximal (e : G ≃g H) (hc : G.Connected) (f : W → ℝ) (v : V) :
    maximal G (f ∘ e) v = maximal H f (e v) := by
  unfold maximal
  apply sup'_congr
  · rw [Fintype.card_congr e.toEquiv]
  · intro r _
    exact iso_ballAverage e hc f v r

theorem iso_variation (e : G ≃g H) (p : ℝ) (f : W → ℝ) :
    variation G p (f ∘ e) = variation H p f := by
  classical
  unfold variation energy
  congr 2
  apply Fintype.sum_equiv e.toEquiv
  intro v
  apply Fintype.sum_equiv e.toEquiv
  intro w
  simp [e.map_rel_iff]

private theorem transfer_admissible (e : G ≃g H) (hc : G.Connected) (p c : ℝ)
    (h : Admissible G p c) : Admissible H p c := by
  refine ⟨h.1, fun f => ?_⟩
  have h' := h.2 (f ∘ e)
  rw [show maximal G (f ∘ e) = maximal H f ∘ e from funext (iso_maximal e hc f),
    iso_variation, iso_variation] at h'
  exact h'

theorem iso_admissible (e : G ≃g H) (hc : G.Connected) (p c : ℝ) :
    Admissible G p c ↔ Admissible H p c :=
  ⟨transfer_admissible e hc p c, transfer_admissible e.symm (e.connected_iff.mp hc) p c⟩

end SharpVariation
