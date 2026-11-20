module

public import SharpVariation.PaperTreeGeometry
public import SharpVariation.PaperTreeLevels
public import SharpVariation.Graph
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The distinguished edges and leaves of the stretched tree

This file formalizes the root, the parallel edges at the final ordinary
branching level, and the lower bound on the ball one step below that level.
See §5 of González-Riquelme–Kovač–Madrid, arXiv:2603.12462.
-/
namespace SharpVariation.PaperTree

abbrev W (k t : ℕ) := Geometry.Vertex k (height t) (exponent t)
abbrev tree (k t : ℕ) := Geometry.graph k (height t) (exponent t)

variable {k : ℕ}

def root (t : ℕ) (hk : 0 < k) : W k t := Geometry.node hk 0 (by omega) 0
def first (t : ℕ) (hk : 0 < k) : W k t := Geometry.node hk 1 (by unfold height; omega) 0

def center (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) : W k t :=
  Geometry.node hk (branchLevel t) (by unfold height; omega) i
def child (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) : W k t :=
  Geometry.node hk (branchLevel t + 1) (by unfold height; omega) i

@[simp] theorem label_center (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    Geometry.label (center t hk i) = i.val := by
  change i.val % k ^ exponent t (branchLevel t) = _
  rw [exponent_level, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem label_child (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    Geometry.label (child t hk i) = i.val := by
  change i.val % k ^ exponent t (branchLevel t + 1) = _
  rw [exponent_next, Nat.mod_eq_of_lt i.isLt]

theorem center_injective (t : ℕ) (hk : 0 < k) : Function.Injective (center t hk) := by
  intro i j h
  have he := congrArg Geometry.label h
  simpa only [label_center, Fin.val_inj] using he

theorem child_injective (t : ℕ) (hk : 0 < k) : Function.Injective (child t hk) := by
  intro i j h
  have he := congrArg Geometry.label h
  simpa only [label_child, Fin.val_inj] using he

theorem center_ne_child (t : ℕ) (hk : 0 < k) (i j : Fin (k^(t+1))) :
    center t hk i ≠ child t hk j := by
  intro h
  have he := congrArg Geometry.depth h
  change branchLevel t = branchLevel t + 1 at he
  omega

theorem adj_center_child (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    (tree k t).Adj (center t hk i) (child t hk i) :=
  Geometry.adj_node (exponent_mono t) hk _ _ _

theorem root_neighbor (t : ℕ) (hk : 0 < k) (z : W k t) :
    (tree k t).Adj (root t hk) z ↔ z = first t hk := by
  constructor
  · intro h
    obtain ⟨h,_⟩ | ⟨h,_⟩ := h
    · change 0 + 1 = Geometry.depth z at h
      apply Geometry.vertex_ext h.symm
      have hz := z.2.isLt
      change Geometry.label z < k ^ exponent t (Geometry.depth z) at hz
      rw [← h, zero_add, exponent_one, pow_zero] at hz
      change Geometry.label z = 0 % k ^ exponent t 1
      simp; omega
    · change Geometry.depth z + 1 = 0 at h
      omega
  · rintro rfl
    exact Geometry.adj_node (exponent_mono t) hk 0 (by unfold height; omega) 0

theorem tree_connected (t : ℕ) (hk : 0 < k) : (tree k t).Connected :=
  Geometry.connected (exponent_mono t) hk (exponent_zero t)

theorem dist_node_root (t : ℕ) (hk : 0 < k) (h : ℕ) (hh : h ≤ height t) (i : ℕ) :
    (tree k t).dist (Geometry.node hk h hh i) (root t hk) = h := by
  let v : W k t := Geometry.node hk h hh i
  have hb := (Geometry.dist_depth (tree_connected t hk) v (root t hk)).2
  change h ≤ 0 + _ at hb
  rw [zero_add] at hb
  apply le_antisymm _ hb
  have hroot : (Geometry.node (e := exponent t) hk 0 (by omega : 0 ≤ height t) i) = root t hk := by
    apply Geometry.vertex_ext
    · rfl
    change i % k ^ exponent t 0 = 0 % k ^ exponent t 0
    simp [exponent_zero, Nat.mod_one]
  obtain ⟨w, hw⟩ := Geometry.vertical_walk (exponent_mono t) hk 0 h (by omega : 0+h ≤ height t) i
  have hup := SimpleGraph.dist_le w
  rw [hw, hroot] at hup
  simpa only [Nat.zero_add, SimpleGraph.dist_comm (u := root t hk)] using hup

theorem dist_center_root (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    (tree k t).dist (center t hk i) (root t hk) = branchLevel t :=
  dist_node_root t hk _ _ _

theorem dist_child_root (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    (tree k t).dist (child t hk i) (root t hk) = branchLevel t + 1 :=
  dist_node_root t hk _ _ _

/-- The k² leaves immediately below the final stalk retain its first t+1 digits. -/
private def leaf (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) (j : Fin (k^2)) : W k t :=
  Geometry.node hk (height t) le_rfl (i.val + k^(t+1)*j.val)

private theorem label_leaf (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) (j : Fin (k^2)) :
    Geometry.label (leaf t hk i j) = i.val + k^(t+1)*j.val := by
  change _ % k ^ exponent t (height t) = _
  rw [exponent_height]
  apply Nat.mod_eq_of_lt
  have hh : t+3 = (t+1)+2 := by omega
  rw [hh, pow_add k (t+1) 2]
  have hr := Nat.mul_le_mul_left (k^(t+1)) j.isLt
  have hi := i.isLt
  nlinarith

private theorem leaf_injective (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    Function.Injective (leaf t hk i) := by
  intro j j' h
  have h' := congrArg Geometry.label h
  rw [label_leaf, label_leaf] at h'
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hk) (Nat.add_left_cancel h'))

private theorem dist_child_leaf (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) (j : Fin (k^2)) :
    (tree k t).dist (child t hk i) (leaf t hk i j) ≤ branchLevel t := by
  let label := i.val + k^(t+1)*j.val
  have he : branchLevel t + 1 + branchLevel t = height t := by unfold height; omega
  obtain ⟨w,hw⟩ := Geometry.vertical_walk (exponent_mono t) hk (branchLevel t+1)
    (branchLevel t) he.le label
  have hup := SimpleGraph.dist_le w
  rw [hw] at hup
  have hstart : (Geometry.node (e := exponent t) hk (branchLevel t+1) (by unfold height; omega : _ ≤ height t) label)
      = child t hk i := by
    apply Geometry.vertex_ext
    · rfl
    rw [label_child]
    change (i.val + k^(t+1)*j.val) % k ^ exponent t (branchLevel t+1) = i.val
    rw [exponent_next, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hend : (Geometry.node (e := exponent t) hk (branchLevel t+1+branchLevel t) he.le label)
      = leaf t hk i j := by
    apply Geometry.vertex_ext he
    change label % k ^ exponent t (branchLevel t+1+branchLevel t) = label % k ^ exponent t (height t)
    rw [he]
  rwa [hstart, hend] at hup

theorem le_child_card (t : ℕ) (hk : 0 < k) (i : Fin (k^(t+1))) :
    k^2 ≤ (closedBall (tree k t) (child t hk i) ((tree k t).dist (child t hk i) (root t hk))).card := by
  classical
  have hmem (j : Fin (k^2)) : leaf t hk i j ∈
      closedBall (tree k t) (child t hk i) ((tree k t).dist (child t hk i) (root t hk)) := by
    apply mem_closedBall.mpr
    rw [dist_child_root]
    exact (dist_child_leaf t hk i j).trans (Nat.le_succ _)
  have hcount := Finset.card_le_card_of_injOn (s := Finset.univ) (leaf t hk i)
    (fun j _ => hmem j) (leaf_injective t hk i).injOn
  simpa using hcount

end SharpVariation.PaperTree
