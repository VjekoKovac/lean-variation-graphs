module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! The index at a level records the choices at the preceding branch points
as base-k digits, with the oldest choice in the least significant digit. -/
namespace SharpVariation.PaperTree
namespace Geometry

abbrev Vertex (k H : ℕ) (e : ℕ → ℕ) :=
  (h : Fin (H+1)) × Fin (k ^ e h.val)

variable {k H : ℕ} {e : ℕ → ℕ}

abbrev depth (u : Vertex k H e) := u.1.val
abbrev label (u : Vertex k H e) := u.2.val

def step (u v : Vertex k H e) : Prop :=
  depth u + 1 = depth v ∧ label u = label v % k ^ e (depth u)

def graph (k H : ℕ) (e : ℕ → ℕ) : SimpleGraph (Vertex k H e) where
  Adj u v := step u v ∨ step v u
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v => by simp [step]⟩

def node (hk : 0 < k) (h : ℕ) (hh : h ≤ H) (i : ℕ) : Vertex k H e :=
  ⟨⟨h, by omega⟩, ⟨i % k ^ e h, Nat.mod_lt _ (Nat.pow_pos hk)⟩⟩

theorem vertex_ext {u v : Vertex k H e} (hd : depth u = depth v) (hi : label u = label v) : u = v := by
  obtain ⟨⟨du,hdu⟩, ⟨iu,hu⟩⟩ := u
  obtain ⟨⟨dv,hdv⟩, ⟨iv,hv⟩⟩ := v
  change du = dv at hd
  subst dv
  change iu = iv at hi
  subst iv
  rfl

theorem node_label (hk : 0 < k) (u : Vertex k H e) :
    node hk (depth u) (Nat.le_of_lt_succ u.1.isLt) (label u) = u :=
  vertex_ext rfl (Nat.mod_eq_of_lt u.2.isLt)

theorem adj_node (he : Monotone e) (hk : 0 < k) (h : ℕ) (hh : h+1 ≤ H) (i : ℕ) :
    (graph k H e).Adj (node hk h (by omega) i) (node hk (h+1) hh i) := by
  apply Or.inl
  refine ⟨rfl, ?_⟩
  change i % k ^ e h = (i % k ^ e (h+1)) % k ^ e h
  exact (Nat.mod_mod_of_dvd _ (pow_dvd_pow _ (he (by omega)))).symm

/-- Vertical paths carrying the same base-k label have the level difference as length. -/
theorem vertical_walk (he : Monotone e) (hk : 0 < k) (h d : ℕ) (hd : h+d ≤ H) (i : ℕ) :
    ∃ w : (graph k H e).Walk (node hk h (by omega) i) (node hk (h+d) hd i), w.length = d := by
  induction d with
  | zero => exact ⟨.nil,rfl⟩
  | succ d ih =>
    obtain ⟨w,hw⟩ := ih (by omega)
    refine ⟨w.concat (adj_node he hk (h+d) hd i), ?_⟩
    simp [hw]

theorem connected (he : Monotone e) (hk : 0 < k) (hzero : e 0 = 0) : (graph k H e).Connected := by
  let root : Vertex k H e := node hk 0 (by omega) 0
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨root, fun u => ?_⟩
  obtain ⟨w,hw⟩ := vertical_walk (H := H) he hk 0 (depth u) (by simpa using Nat.le_of_lt_succ u.1.isLt) (label u)
  have hs : root = node (e := e) hk 0 (by omega : 0 ≤ H) (label u) := by
    apply vertex_ext (u := root) (v := node (e := e) hk 0 (by omega : 0 ≤ H) (label u)) (by rfl)
    change 0 % k ^ e 0 = label u % k ^ e 0
    simp [hzero,Nat.mod_one]
  have ht : node (e := e) hk (0+depth u) (by simpa only [Nat.zero_add] using Nat.le_of_lt_succ u.1.isLt) (label u) = u := by
    apply vertex_ext (Nat.zero_add _)
    simp [node, Nat.mod_eq_of_lt u.2.isLt]
  exact Eq.mp (congrArg₂ (graph k H e).Reachable hs.symm ht) ⟨w⟩

theorem walk_depth {u v : Vertex k H e} (w : (graph k H e).Walk u v) :
    depth v ≤ depth u + w.length ∧ depth u ≤ depth v + w.length := by
  induction w with
  | nil => simp
  | cons h w ih =>
    simp only [SimpleGraph.Walk.length_cons]
    change step _ _ ∨ step _ _ at h
    rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> constructor <;> omega

theorem dist_depth (hc : (graph k H e).Connected) (u v : Vertex k H e) :
    depth v ≤ depth u + (graph k H e).dist u v ∧ depth u ≤ depth v + (graph k H e).dist u v := by
  obtain ⟨w,hw⟩ := hc.exists_walk_length_eq_dist u v
  simpa [←hw] using walk_depth w

theorem walk_prefix (he : Monotone e) (a : ℕ) {u v : Vertex k H e}
    (w : (graph k H e).Walk u v)
    (h : w.length + 2*a ≤ depth u + depth v + 1) :
    label u % k ^ e a = label v % k ^ e a := by
  induction w with
  | nil => rfl
  | @cons u z v edge tail ih =>
    simp only [SimpleGraph.Walk.length_cons] at h
    have bd := walk_depth tail
    have ez : depth u ≤ depth z + 1 ∧ depth z ≤ depth u + 1 := by
      rcases edge with ⟨h,_⟩ | ⟨h,_⟩ <;> omega
    have hu : a ≤ depth u := by omega
    have hz : a ≤ depth z := by omega
    apply Eq.trans _ (ih (by omega))
    rcases edge with ⟨_,huv⟩ | ⟨_,hvu⟩
    · rw [huv, Nat.mod_mod_of_dvd _ (pow_dvd_pow _ (he hu))]
    · rw [hvu, Nat.mod_mod_of_dvd _ (pow_dvd_pow _ (he hz))]

end Geometry
end SharpVariation.PaperTree
