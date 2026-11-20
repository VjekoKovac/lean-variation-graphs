module

public import Mathlib.Combinatorics.SimpleGraph.Basic
@[expose] public section

namespace SharpVariation.Four

def edgeIndex (a b : Fin 4) : ℕ :=
  let i := min a b
  let j := max a b
  if i = 0 then j.val - 1 else if i = 1 then j.val + 1 else 5

/-- Bits zero through five encode edges 01, 02, 03, 12, 13, 23 respectively. -/
def graphOfMask (m : ℕ) : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ m.testBit (edgeIndex a b) = true
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa only [edgeIndex, min_comm b a, max_comm b a] using h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (m : ℕ) : DecidableRel (graphOfMask m).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ m.testBit (edgeIndex a b) = true))

end SharpVariation.Four
