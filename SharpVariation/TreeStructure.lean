module

public import SharpVariation.PaperTreeLeaves
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace SharpVariation.PaperTree
open Geometry

/-- An edge from a vertex to a neighbor of no greater depth must point to
the parent. Both the depth and the label of that parent are forced. -/
private theorem unique_parent {k H : ℕ} {e : ℕ → ℕ} {u v w : Vertex k H e}
    (hv : (graph k H e).Adj u v) (hw : (graph k H e).Adj u w)
    (hdv : depth v ≤ depth u) (hdw : depth w ≤ depth u) : v = w := by
  have p {q : Vertex k H e} (h : (graph k H e).Adj u q) (h' : depth q ≤ depth u) :
      step q u := by
    rcases h with ⟨h,_⟩ | h
    · omega
    · exact h
  obtain ⟨h₁,hl₁⟩ := p hv hdv
  obtain ⟨h₂,hl₂⟩ := p hw hdw
  have h : depth v = depth w := by omega
  apply vertex_ext h
  rw [hl₁,hl₂,h]

/-- The actual graph used for the large constant is a tree. Rotate any
hypothetical cycle to a vertex of maximum depth. Its two neighbors would
then be the same parent, contradicting simplicity of the cycle. -/
theorem tree_isTree {k : ℕ} (t : ℕ) (hk : 0 < k) : (tree k t).IsTree := by
  classical
  refine ⟨tree_connected t hk, ?_⟩
  intro v walk cycle
  obtain ⟨a,ha,hmax⟩ := walk.support.toFinset.exists_max_image depth
    ⟨v,List.mem_toFinset.mpr walk.start_mem_support⟩
  let q := walk.rotate a (List.mem_toFinset.mp ha)
  have hc : q.IsCycle := (SimpleGraph.Walk.isCycle_rotate _).mpr cycle
  have hq (i : ℕ) : depth (q.getVert i) ≤ depth a := by
    apply hmax
    apply List.mem_toFinset.mpr
    exact (walk.mem_support_rotate_iff a _).mp (q.getVert_mem_support i)
  exact hc.snd_ne_penultimate
    (unique_parent (q.adj_snd hc.not_nil) (q.adj_penultimate hc.not_nil).symm (hq 1) (hq _))

end SharpVariation.PaperTree
