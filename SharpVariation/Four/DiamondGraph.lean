module

public import SharpVariation.Four.Diamond
public import SharpVariation.Four.Reduction
public import SharpVariation.Four.Balls
public import SharpVariation.Four.Mask

@[expose] public section

namespace SharpVariation.Four
open Finset

set_option maxHeartbeats 5000000

private theorem ball0 (r : Fin 5) : closedBall (graphOfMask 61) 0 r =
    (![{0}, {0, 1, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}] : Fin 5 → Finset (Fin 4)) r := by
  rw [closedBall_eq_searchBall (graphOfMask 61) (fun x y => decide ((graphOfMask 61).Adj x y)) (by simp) 0 r 3 (by decide)]
  revert r
  decide

private theorem max0 (f : Fin 4 → ℝ) : maximal (graphOfMask 61) f 0 =
    (max |f 0| (max ((|f 0| + |f 1| + |f 3|) / 3) ((|f 0| + |f 1| + |f 2| + |f 3|) / 4))) := by
  rw [maximal_four]
  simp only [ballAverage]
  have b0 : closedBall (graphOfMask 61) 0 0 = {0} := ball0 0
  have b1 : closedBall (graphOfMask 61) 0 1 = {0, 1, 3} := ball0 1
  have b2 : closedBall (graphOfMask 61) 0 2 = {0, 1, 2, 3} := ball0 2
  have b3 : closedBall (graphOfMask 61) 0 3 = {0, 1, 2, 3} := ball0 3
  have b4 : closedBall (graphOfMask 61) 0 4 = {0, 1, 2, 3} := ball0 4
  rw [b0, b1, b2, b3, b4]
  norm_num [Finset.sum_insert, Finset.card_insert_of_notMem, max_self, add_assoc]

private theorem ball1 (r : Fin 5) : closedBall (graphOfMask 61) 1 r =
    (![{1}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}] : Fin 5 → Finset (Fin 4)) r := by
  rw [closedBall_eq_searchBall (graphOfMask 61) (fun x y => decide ((graphOfMask 61).Adj x y)) (by simp) 1 r 3 (by decide)]
  revert r
  decide

private theorem max1 (f : Fin 4 → ℝ) : maximal (graphOfMask 61) f 1 =
    (max |f 1| ((|f 0| + |f 1| + |f 2| + |f 3|) / 4)) := by
  rw [maximal_four]
  simp only [ballAverage]
  have b0 : closedBall (graphOfMask 61) 1 0 = {1} := ball1 0
  have b1 : closedBall (graphOfMask 61) 1 1 = {0, 1, 2, 3} := ball1 1
  have b2 : closedBall (graphOfMask 61) 1 2 = {0, 1, 2, 3} := ball1 2
  have b3 : closedBall (graphOfMask 61) 1 3 = {0, 1, 2, 3} := ball1 3
  have b4 : closedBall (graphOfMask 61) 1 4 = {0, 1, 2, 3} := ball1 4
  rw [b0, b1, b2, b3, b4]
  norm_num [Finset.sum_insert, Finset.card_insert_of_notMem, max_self, add_assoc]

private theorem ball2 (r : Fin 5) : closedBall (graphOfMask 61) 2 r =
    (![{2}, {1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}] : Fin 5 → Finset (Fin 4)) r := by
  rw [closedBall_eq_searchBall (graphOfMask 61) (fun x y => decide ((graphOfMask 61).Adj x y)) (by simp) 2 r 3 (by decide)]
  revert r
  decide

private theorem max2 (f : Fin 4 → ℝ) : maximal (graphOfMask 61) f 2 =
    (max |f 2| (max ((|f 1| + |f 2| + |f 3|) / 3) ((|f 0| + |f 1| + |f 2| + |f 3|) / 4))) := by
  rw [maximal_four]
  simp only [ballAverage]
  have b0 : closedBall (graphOfMask 61) 2 0 = {2} := ball2 0
  have b1 : closedBall (graphOfMask 61) 2 1 = {1, 2, 3} := ball2 1
  have b2 : closedBall (graphOfMask 61) 2 2 = {0, 1, 2, 3} := ball2 2
  have b3 : closedBall (graphOfMask 61) 2 3 = {0, 1, 2, 3} := ball2 3
  have b4 : closedBall (graphOfMask 61) 2 4 = {0, 1, 2, 3} := ball2 4
  rw [b0, b1, b2, b3, b4]
  norm_num [Finset.sum_insert, Finset.card_insert_of_notMem, max_self, add_assoc]

private theorem ball3 (r : Fin 5) : closedBall (graphOfMask 61) 3 r =
    (![{3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}] : Fin 5 → Finset (Fin 4)) r := by
  rw [closedBall_eq_searchBall (graphOfMask 61) (fun x y => decide ((graphOfMask 61).Adj x y)) (by simp) 3 r 3 (by decide)]
  revert r
  decide

private theorem max3 (f : Fin 4 → ℝ) : maximal (graphOfMask 61) f 3 =
    (max |f 3| ((|f 0| + |f 1| + |f 2| + |f 3|) / 4)) := by
  rw [maximal_four]
  simp only [ballAverage]
  have b0 : closedBall (graphOfMask 61) 3 0 = {3} := ball3 0
  have b1 : closedBall (graphOfMask 61) 3 1 = {0, 1, 2, 3} := ball3 1
  have b2 : closedBall (graphOfMask 61) 3 2 = {0, 1, 2, 3} := ball3 2
  have b3 : closedBall (graphOfMask 61) 3 3 = {0, 1, 2, 3} := ball3 3
  have b4 : closedBall (graphOfMask 61) 3 4 = {0, 1, 2, 3} := ball3 4
  rw [b0, b1, b2, b3, b4]
  norm_num [Finset.sum_insert, Finset.card_insert_of_notMem, max_self, add_assoc]

private theorem var_expanded (f : Fin 4 → ℝ) : variation (graphOfMask 61) 1 f = 
    |f 0 - f 1| + |f 0 - f 3| + |f 1 - f 2| + |f 1 - f 3| + |f 2 - f 3| := by
  have a00 : ¬ (graphOfMask 61).Adj 0 0 := by decide
  have a01 : (graphOfMask 61).Adj 0 1 := by decide
  have a02 : ¬ (graphOfMask 61).Adj 0 2 := by decide
  have a03 : (graphOfMask 61).Adj 0 3 := by decide
  have a10 : (graphOfMask 61).Adj 1 0 := by decide
  have a11 : ¬ (graphOfMask 61).Adj 1 1 := by decide
  have a12 : (graphOfMask 61).Adj 1 2 := by decide
  have a13 : (graphOfMask 61).Adj 1 3 := by decide
  have a20 : ¬ (graphOfMask 61).Adj 2 0 := by decide
  have a21 : (graphOfMask 61).Adj 2 1 := by decide
  have a22 : ¬ (graphOfMask 61).Adj 2 2 := by decide
  have a23 : (graphOfMask 61).Adj 2 3 := by decide
  have a30 : (graphOfMask 61).Adj 3 0 := by decide
  have a31 : (graphOfMask 61).Adj 3 1 := by decide
  have a32 : (graphOfMask 61).Adj 3 2 := by decide
  have a33 : ¬ (graphOfMask 61).Adj 3 3 := by decide
  simp only [variation, energy, div_one, Real.rpow_one, Fin.sum_univ_four,
    ite_eq_right a00, ite_eq_left a01, ite_eq_right a02, ite_eq_left a03, ite_eq_left a10, ite_eq_right a11, ite_eq_left a12, ite_eq_left a13, ite_eq_right a20, ite_eq_left a21, ite_eq_right a22, ite_eq_left a23, ite_eq_left a30, ite_eq_left a31, ite_eq_left a32, ite_eq_right a33, add_zero, zero_add]
  rw [abs_sub_comm (f 1) (f 0), abs_sub_comm (f 3) (f 0), abs_sub_comm (f 2) (f 1), abs_sub_comm (f 3) (f 1), abs_sub_comm (f 3) (f 2)]
  ring

/-- Both the sharp upper bound and its optimality for mask 61 (diamond). -/
theorem diamondSharp : IsLeast {c : ℝ | Admissible (graphOfMask 61) 1 c} (3 / 4) := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro f
    rw [var_expanded, var_expanded]
    have upper := diamondUpper |f 0| |f 1| |f 2| |f 3| (maximal (graphOfMask 61) f 0) (maximal (graphOfMask 61) f 1) (maximal (graphOfMask 61) f 2) (maximal (graphOfMask 61) f 3) (max0 f) (max1 f) (max2 f) (max3 f)
    exact upper.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add (add_le_add (abs_contract f 0 1) (abs_contract f 0 3)) (abs_contract f 1 2)) (abs_contract f 1 3)) (abs_contract f 2 3)) (by norm_num))
  · intro c hc
    let f : Fin 4 → ℝ := fun i => if i = 1 then 1 else 0
    have h := hc.2 f
    rw [var_expanded, var_expanded] at h
    simp only [max0, max1, max2, max3] at h
    norm_num [f] at h ⊢
    linarith

end SharpVariation.Four
