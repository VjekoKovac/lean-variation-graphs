module

public import SharpVariation.Defs

@[expose] public section
namespace SharpVariation.Four

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices reached in at most the indicated number of steps. The Boolean adjacency
table makes the finite searches on four vertices reducible by Lean's kernel. -/
def searchBall (adj : V → V → Bool) (v : V) : ℕ → Finset V
  | 0 => {v}
  | r + 1 =>
    insert v ((Finset.univ.filter fun w => adj v w).biUnion fun w => searchBall adj w r)

/-- Correctness of the bounded walk search, including radius zero. -/
theorem mem_searchBall_iff (G : SimpleGraph V) (adj : V → V → Bool)
    (hadj : ∀ x y, adj x y = true ↔ G.Adj x y) (v w : V) (r : ℕ) :
    w ∈ searchBall adj v r ↔ ∃ p : G.Walk v w, p.length ≤ r := by
  induction r generalizing v w with
  | zero =>
    simp only [searchBall, Finset.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      exact ⟨.nil, rfl⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => rfl
      | cons h p => simp at hp
  | succ r ih =>
    simp only [searchBall, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, hadj, ih]
    constructor
    · rintro (rfl | ⟨x, h, p, hp⟩)
      · exact ⟨.nil, Nat.zero_le _⟩
      · exact ⟨.cons h p, by simpa using hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl rfl
      | @cons u x w h p =>
        exact Or.inr ⟨x, h, p, by simpa using hp⟩

/-- A successful finite search from the center certifies reachability of every vertex.
On this component the ordinary natural-number graph distance recovers the search ball.
The proof uses Mathlib's shortest-walk existence and its distance bound for each walk. -/
theorem closedBall_eq_searchBall (G : SimpleGraph V) (adj : V → V → Bool)
    (hadj : ∀ x y, adj x y = true ↔ G.Adj x y) (v : V) (r R : ℕ)
    (hall : searchBall adj v R = Finset.univ) :
    closedBall G v r = searchBall adj v r := by
  classical
  ext w
  rw [mem_searchBall_iff G adj hadj]
  simp only [closedBall, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hm : w ∈ searchBall adj v R := hall ▸ Finset.mem_univ _
    obtain ⟨q, _⟩ := (mem_searchBall_iff G adj hadj v w R).mp hm
    obtain ⟨p, hp⟩ := q.reachable.exists_walk_length_eq_dist
    exact ⟨p, hp.trans_le h⟩
  · rintro ⟨p, hp⟩
    exact (SimpleGraph.dist_le p).trans hp

end SharpVariation.Four
