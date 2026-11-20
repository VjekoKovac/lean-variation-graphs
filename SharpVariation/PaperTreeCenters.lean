module

public import SharpVariation.PaperTreeGeometry
public import SharpVariation.PaperTreeLevels
public import SharpVariation.Graph
public import Mathlib.Data.Fintype.Prod

@[expose] public section
namespace SharpVariation.PaperTree

open Geometry

/-- In the source tree, the root-reaching ball at a branching child contains at
most k vertices of each depth. Divide a vertex label by k^(e(floor(h/2))).
Its remainder is already determined by the center and its depth h. -/
theorem center_card_le (t k : ℕ) (hk : 0 < k)
    (u : Vertex k (height t) (exponent t)) (hu : depth u = branchLevel t) :
    (closedBall (graph k (height t) (exponent t)) u (branchLevel t)).card ≤
      (height t + 1) * k := by
  classical
  let G := graph k (height t) (exponent t)
  let s := closedBall G u (branchLevel t)
  let modulus (h : ℕ) := k ^ exponent t (h/2)
  have hc : G.Connected := connected (exponent_mono t) hk (exponent_zero t)
  have reach (z : s) : G.dist u z.val ≤ branchLevel t := mem_closedBall.mp z.property
  have hdepth (z : s) : depth z.val < height t := by
    have h := (dist_depth hc u z.val).1
    change depth z.val ≤ depth u + G.dist u z.val at h
    have := reach z
    unfold height
    omega
  have hquot (z : s) : label z.val / modulus (depth z.val) < k := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos hk)).mpr
    have hpow : k ^ exponent t (depth z.val) ≤ k ^ (exponent t (depth z.val / 2) + 1) :=
      pow_le_pow_right' hk (exponent_half t _ (hdepth z))
    have := z.val.2.isLt.trans_le hpow
    simpa only [modulus, pow_succ, Nat.mul_comm k] using this
  have hprefix (z : s) :
      label z.val % modulus (depth z.val) = label u % modulus (depth z.val) := by
    obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist u z.val
    have hz := reach z
    apply (walk_prefix (exponent_mono t) (depth z.val / 2) w ?_).symm
    omega
  let code (z : s) : Fin (height t + 1) × Fin k :=
    (z.val.1, ⟨label z.val / modulus (depth z.val), hquot z⟩)
  have hinj : Function.Injective code := by
    intro x y hxy
    have hd : depth x.val = depth y.val := congrArg (fun a => a.1.val) hxy
    have hq : label x.val / modulus (depth x.val) = label y.val / modulus (depth y.val) :=
      congrArg (fun a => a.2.val) hxy
    have hr := (hprefix x).trans ((congrArg (fun h => label u % modulus h) hd).trans (hprefix y).symm)
    rw [hd] at hq hr
    apply Subtype.ext
    apply vertex_ext hd
    calc
      label x.val = label x.val % modulus (depth y.val) +
          modulus (depth y.val) * (label x.val / modulus (depth y.val)) := (Nat.mod_add_div _ _).symm
      _ = label y.val := by rw [hr, hq, Nat.mod_add_div]
  change s.card ≤ _
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective code hinj

end SharpVariation.PaperTree
