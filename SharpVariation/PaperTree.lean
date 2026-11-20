module

public import SharpVariation.PaperTreeCenters
public import SharpVariation.PaperTreeLeaves
public import SharpVariation.TreeDirac
public import SharpVariation.TreeGrowth

@[expose] public section
noncomputable section

namespace SharpVariation.PaperTree

/-- The proof of Theorem 4 in arXiv:2603.12462v1, with the point mass at the root
of the tree constructed in Section 5. We can take C_m = height (m-1) + 1. -/
theorem large_witness (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), G.Connected ∧
      ∃ f : W → ℝ, C * variation G p f < variation G p (maximal G f) := by
  obtain ⟨t,ht⟩ := exists_nat_gt p
  have hm : p < ((t+1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨k,hk,hBD,hgain⟩ :=
    tree_growth (m := t+1) (D := height t+1) hm hp (Nat.succ_pos _) hC
  have hk' : 0 < k := by omega
  let G := tree k t
  let v := root t hk'
  have hc : G.Connected := tree_connected t hk'
  have hsmall (i : Fin (k^(t+1))) :
      (closedBall G (center t hk' i) (G.dist (center t hk' i) v)).card ≤ (height t+1)*k := by
    change (closedBall (tree k t) _ ((tree k t).dist _ (root t hk'))).card ≤ _
    rw [dist_center_root]
    exact center_card_le t k hk' _ rfl
  obtain ⟨hinput,houtput⟩ := TreeExample.tree_dirac_energy hc v (first t hk')
    (center t hk') (child t hk') (root_neighbor t hk') (center_injective t hk')
    (child_injective t hk') (center_ne_child t hk') (adj_center_child t hk')
    (Nat.mul_pos (Nat.succ_pos _) hk') hBD hsmall (le_child_card t hk') p hp
  refine ⟨W k t, inferInstance, G, hc, TreeExample.dirac v, ?_⟩
  rw [hinput, mul_one, variation]
  simp only [Fintype.card_fin] at houtput
  have hh := Real.rpow_lt_rpow (Real.rpow_nonneg hC.le p) (hgain.trans_le houtput) (one_div_pos.mpr hp)
  simpa [one_div, Real.rpow_rpow_inv hC.le hp.ne'] using hh

end SharpVariation.PaperTree
