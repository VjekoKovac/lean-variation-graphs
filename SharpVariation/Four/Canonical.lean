module

public import SharpVariation.Four.Classification
public import SharpVariation.Four.PathGraph
public import SharpVariation.Four.CycleGraph
public import SharpVariation.Four.PawGraph
public import SharpVariation.Four.DiamondGraph
public import SharpVariation.Four.StarGraph
public import SharpVariation.Four.CompleteGraph

@[expose] public section

namespace SharpVariation.Four

/-- The six representatives from the four-vertex classification all have
the same sharp one-variation constant. -/
theorem representativeSharp {k : ℕ} (hk : k ∈ representatives) :
    IsLeast {c : ℝ | Admissible (graphOfMask k) 1 c} (3 / 4) := by
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pathSharp
  · exact cycleSharp
  · exact pawSharp
  · exact diamondSharp
  · exact starSharp
  · exact completeSharp

end SharpVariation.Four
