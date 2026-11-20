module

public import SharpVariation.Four.Mask
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! All simple connected graphs on four labelled vertices. Each row of the
classification table specifies either an isomorphism or a separating cut.
The proof checks the entire table against adjacency by kernel reduction. -/
namespace SharpVariation.Four

private def code (a b c d e f : Bool) : ℕ :=
  a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat + 16*e.toNat + 32*f.toNat

private theorem code_spec : ∀ a b c d e f : Bool,
    let m := code a b c d e f
    m < 64 ∧ m.testBit 0 = a ∧ m.testBit 1 = b ∧ m.testBit 2 = c ∧
    m.testBit 3 = d ∧ m.testBit 4 = e ∧ m.testBit 5 = f := by decide

private theorem encode (G : SimpleGraph (Fin 4)) :
    ∃ m : Fin 64, G = graphOfMask m := by
  classical
  let m := code (decide (G.Adj 0 1)) (decide (G.Adj 0 2)) (decide (G.Adj 0 3))
    (decide (G.Adj 1 2)) (decide (G.Adj 1 3)) (decide (G.Adj 2 3))
  obtain ⟨hm, h0, h1, h2, h3, h4, h5⟩ := code_spec (decide (G.Adj 0 1))
    (decide (G.Adj 0 2)) (decide (G.Adj 0 3))
    (decide (G.Adj 1 2)) (decide (G.Adj 1 3)) (decide (G.Adj 2 3))
  change m < 64 at hm
  change m.testBit 0 = _ at h0
  change m.testBit 1 = _ at h1
  change m.testBit 2 = _ at h2
  change m.testBit 3 = _ at h3
  change m.testBit 4 = _ at h4
  change m.testBit 5 = _ at h5
  refine ⟨⟨m, hm⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · change G.Adj 0 1 ↔ (0 : Fin 4) ≠ 1 ∧ m.testBit 0 = true
    rw [h0, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 0 2 ↔ (0 : Fin 4) ≠ 2 ∧ m.testBit 1 = true
    rw [h1, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 0 3 ↔ (0 : Fin 4) ≠ 3 ∧ m.testBit 2 = true
    rw [h2, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 1 0 ↔ (1 : Fin 4) ≠ 0 ∧ m.testBit 0 = true
    rw [h0, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · simp
  · change G.Adj 1 2 ↔ (1 : Fin 4) ≠ 2 ∧ m.testBit 3 = true
    rw [h3, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 1 3 ↔ (1 : Fin 4) ≠ 3 ∧ m.testBit 4 = true
    rw [h4, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 2 0 ↔ (2 : Fin 4) ≠ 0 ∧ m.testBit 1 = true
    rw [h1, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · change G.Adj 2 1 ↔ (2 : Fin 4) ≠ 1 ∧ m.testBit 3 = true
    rw [h3, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · simp
  · change G.Adj 2 3 ↔ (2 : Fin 4) ≠ 3 ∧ m.testBit 5 = true
    rw [h5, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h⟩, And.right⟩
  · change G.Adj 3 0 ↔ (3 : Fin 4) ≠ 0 ∧ m.testBit 2 = true
    rw [h2, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · change G.Adj 3 1 ↔ (3 : Fin 4) ≠ 1 ∧ m.testBit 4 = true
    rw [h4, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · change G.Adj 3 2 ↔ (3 : Fin 4) ≠ 2 ∧ m.testBit 5 = true
    rw [h5, decide_eq_true_eq]
    exact ⟨fun h => ⟨by decide, h.symm⟩, fun h => h.2.symm⟩
  · simp

/-- A zero tag supplies the two sides of a cut. A nonzero tag supplies
the target edge mask and the images of the four vertices. -/
private def certificate : Fin 64 → ℕ × (Fin 4 → Fin 4) :=
  ![(0, ![1, 0, 0, 0]), (0, ![1, 1, 0, 0]),
    (0, ![1, 0, 1, 0]), (0, ![1, 1, 1, 0]),
    (0, ![1, 0, 0, 1]), (0, ![1, 1, 0, 1]),
    (0, ![1, 0, 1, 1]), (7, ![0, 1, 2, 3]),
    (0, ![1, 0, 0, 0]), (0, ![1, 1, 1, 0]),
    (0, ![1, 1, 1, 0]), (0, ![1, 1, 1, 0]),
    (0, ![1, 0, 0, 1]), (41, ![1, 2, 3, 0]),
    (41, ![1, 3, 2, 0]), (39, ![0, 2, 3, 1]),
    (0, ![1, 0, 0, 0]), (0, ![1, 1, 0, 1]),
    (0, ![1, 0, 1, 0]), (41, ![1, 2, 0, 3]),
    (0, ![1, 1, 0, 1]), (0, ![1, 1, 0, 1]),
    (41, ![1, 3, 0, 2]), (39, ![0, 2, 1, 3]),
    (0, ![1, 0, 0, 0]), (7, ![1, 0, 2, 3]),
    (41, ![0, 2, 1, 3]), (39, ![2, 0, 3, 1]),
    (41, ![0, 2, 3, 1]), (39, ![2, 0, 1, 3]),
    (45, ![0, 2, 1, 3]), (61, ![1, 3, 0, 2]),
    (0, ![1, 0, 0, 0]), (0, ![1, 1, 0, 0]),
    (0, ![1, 0, 1, 1]), (41, ![1, 0, 2, 3]),
    (0, ![1, 0, 1, 1]), (41, ![1, 0, 3, 2]),
    (0, ![1, 0, 1, 1]), (39, ![0, 1, 2, 3]),
    (0, ![1, 0, 0, 0]), (41, ![0, 1, 2, 3]),
    (7, ![1, 2, 0, 3]), (39, ![2, 3, 0, 1]),
    (41, ![0, 3, 2, 1]), (45, ![0, 1, 2, 3]),
    (39, ![2, 1, 0, 3]), (61, ![1, 0, 3, 2]),
    (0, ![1, 0, 0, 0]), (41, ![0, 1, 3, 2]),
    (41, ![0, 3, 1, 2]), (45, ![0, 1, 3, 2]),
    (7, ![1, 2, 3, 0]), (39, ![2, 3, 1, 0]),
    (39, ![2, 1, 3, 0]), (61, ![1, 0, 2, 3]),
    (0, ![1, 0, 0, 0]), (39, ![1, 0, 2, 3]),
    (39, ![1, 2, 0, 3]), (61, ![0, 1, 3, 2]),
    (39, ![1, 2, 3, 0]), (61, ![0, 1, 2, 3]),
    (61, ![0, 2, 1, 3]), (63, ![0, 1, 2, 3])]

/-- Representatives in the order path, cycle, paw, diamond, star, complete graph. -/
def representatives : List ℕ := [41, 45, 39, 61, 7, 63]

private def Valid (m : Fin 64) : Prop :=
  let k := (certificate m).1
  let f := (certificate m).2
  if k = 0 then
    (∃ i : Fin 4, f 0 ≠ f i) ∧ (∀ i j, (graphOfMask m).Adj i j → f i = f j)
  else k ∈ representatives ∧ Function.Bijective f ∧
    ∀ i j, (graphOfMask m).Adj i j ↔ (graphOfMask k).Adj (f i) (f j)

private instance (m : Fin 64) : Decidable (Valid m) := by
  unfold Valid
  dsimp only
  infer_instance

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem valid_all : ∀ m, Valid m := by decide

private theorem cut_constant {G : SimpleGraph (Fin 4)} (hG : G.Connected)
    (f : Fin 4 → Fin 4) (h : ∀ i j, G.Adj i j → f i = f j) (i : Fin 4) :
    f 0 = f i := by
  obtain ⟨w⟩ := hG 0 i
  have hw {a b : Fin 4} (v : G.Walk a b) : f a = f b := by
    induction v with
    | nil => rfl
    | cons edge _ ih => exact (h _ _ edge).trans ih
  exact hw w

/-- An isomorphism to one of the six representatives for every connected graph. -/
theorem classify (G : SimpleGraph (Fin 4)) (hG : G.Connected) :
    ∃ k ∈ representatives, Nonempty (G ≃g graphOfMask k) := by
  classical
  obtain ⟨m, rfl⟩ := encode G
  have h := valid_all m
  unfold Valid at h
  dsimp only at h
  split at h
  · obtain ⟨⟨i, hi⟩, he⟩ := h
    exact (hi (cut_constant hG _ he i)).elim
  · obtain ⟨hk, hbij, hadj⟩ := h
    exact ⟨_, hk, ⟨⟨Equiv.ofBijective _ hbij, (hadj _ _).symm⟩⟩⟩

end SharpVariation.Four
