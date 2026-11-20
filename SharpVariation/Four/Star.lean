module
public import SharpVariation.Four.Tools

@[expose] public section

/-! Machine-generated exact dual certificates; see `scripts/four_certificates.py`. -/
namespace SharpVariation.Four

set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

private theorem signed0 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1) / 2) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (l20 : x2 ≤ y2)
    (l21 : ((x0 + x2) / 2) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x3) / 2) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (3 : ℝ) * y0 + (-1 : ℝ) * y1 + (-1 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u0 with u0 | u0
  · linear_combination 3 * u0 + l11 + l22 + l31 + (3 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination 3 * u0 + l11 + l20 + l30 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2

private theorem signed1 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1) / 2) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (l20 : x2 ≤ y2)
    (l21 : ((x0 + x2) / 2) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x3) / 2) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (1 : ℝ) * y0 + (-1 : ℝ) * y1 + (-1 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u0 with u0 | u0
  all_goals rcases u3 with u3 | u3 | u3
  · linear_combination u0 + (1 / 2 : ℝ) * l11 + (1 / 2 : ℝ) * l12 + (1 / 2 : ℝ) * l20 + (1 / 2 : ℝ) * l22 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + l11 + (2 / 3 : ℝ) * l20 + (1 / 3 : ℝ) * l22 + u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (1 / 6 : ℝ) * p2 + (7 / 12 : ℝ) * n2
  · linear_combination u0 + l11 + l20 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination u0 + l12 + l22 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + l11 + l20 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + l11 + l20 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2

private theorem signed2 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1) / 2) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x0 + x2) / 2) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x3) / 2) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (1 : ℝ) * y0 + (-1 : ℝ) * y1 + (1 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u0 with u0 | u0
  all_goals rcases u2 with u2 | u2 | u2
  · linear_combination u0 + (1 / 2 : ℝ) * l11 + (1 / 2 : ℝ) * l12 + u2 + (1 / 2 : ℝ) * l30 + (1 / 2 : ℝ) * l32 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + l11 + u2 + (2 / 3 : ℝ) * l30 + (1 / 3 : ℝ) * l32 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (1 / 6 : ℝ) * p1 + (7 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + l11 + u2 + l30 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + l12 + u2 + l32 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination u0 + l11 + u2 + l30 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + l11 + u2 + l30 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2

private theorem signed3 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1) / 2) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x0 + x2) / 2) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x3) / 2) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (-1 : ℝ) * y0 + (-1 : ℝ) * y1 + (1 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u2 with u2 | u2 | u2
  all_goals rcases u3 with u3 | u3 | u3
  · linear_combination l01 + l11 + u2 + u3 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l01 + l11 + u2 + u3 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l01 + l12 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l01 + l11 + u2 + u3 + (3 / 4 : ℝ) * p0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + l11 + u2 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l00 + l12 + u2 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l01 + l12 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + l12 + u2 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l00 + l11 + u2 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2

private theorem signed4 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1) / 2) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x0 + x2) / 2) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x3) / 2) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (1 : ℝ) * y0 + (1 : ℝ) * y1 + (-1 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u0 with u0 | u0
  all_goals rcases u1 with u1 | u1 | u1
  · linear_combination u0 + u1 + (1 / 2 : ℝ) * l21 + (1 / 2 : ℝ) * l22 + (1 / 2 : ℝ) * l30 + (1 / 2 : ℝ) * l32 + (3 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + u1 + l21 + (2 / 3 : ℝ) * l30 + (1 / 3 : ℝ) * l32 + (1 / 6 : ℝ) * p0 + (7 / 12 : ℝ) * n0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + u1 + l21 + l30 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + u1 + l22 + l32 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination u0 + u1 + l21 + l30 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + u1 + l21 + l30 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2

private theorem signed5 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1) / 2) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x0 + x2) / 2) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x3) / 2) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (-1 : ℝ) * y0 + (1 : ℝ) * y1 + (-1 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u1 with u1 | u1 | u1
  all_goals rcases u3 with u3 | u3 | u3
  · linear_combination l00 + u1 + l22 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + u1 + l22 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l01 + u1 + l22 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l00 + u1 + l22 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + u1 + l21 + u3 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l00 + u1 + l22 + u3 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l01 + u1 + l22 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + u1 + l22 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l00 + u1 + l21 + u3 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2

private theorem signed6 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1) / 2) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x0 + x2) / 2) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x3) / 2) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (-1 : ℝ) * y0 + (1 : ℝ) * y1 + (1 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u1 with u1 | u1 | u1
  all_goals rcases u2 with u2 | u2 | u2
  · linear_combination l01 + u1 + u2 + l31 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination l01 + u1 + u2 + l31 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination l01 + u1 + u2 + l32 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l01 + u1 + u2 + l31 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination l00 + u1 + u2 + l31 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination l00 + u1 + u2 + l32 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l01 + u1 + u2 + l32 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l00 + u1 + u2 + l32 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l00 + u1 + u2 + l31 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2

private theorem signed7 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1) / 2) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x0 + x2) / 2) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x3) / 2) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x2 ≤ |x0 - x2|)
    (n1 : -(x0 - x2) ≤ |x0 - x2|)
    (p2 : x0 - x3 ≤ |x0 - x3|)
    (n2 : -(x0 - x3) ≤ |x0 - x3|)
    : (-3 : ℝ) * y0 + (1 : ℝ) * y1 + (1 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  rcases u1 with u1 | u1 | u1
  all_goals rcases u2 with u2 | u2 | u2
  all_goals rcases u3 with u3 | u3 | u3
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination 3 * l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 3 * l00 + u1 + u2 + u3 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination 3 * l00 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 3 * l00 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination 3 * l01 + u1 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l00 + 2 * l01 + u1 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 3 * l00 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination 3 * l01 + u1 + u2 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 2 * l00 + l01 + u1 + u2 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination 3 * l00 + u1 + u2 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * n2

/-- The real piecewise-linear upper bound for the star graph. -/
theorem starUpper (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (h0 : y0 = (max x0 ((x0 + x1 + x2 + x3) / 4)))
    (h1 : y1 = (max x1 (max ((x0 + x1) / 2) ((x0 + x1 + x2 + x3) / 4))))
    (h2 : y2 = (max x2 (max ((x0 + x2) / 2) ((x0 + x1 + x2 + x3) / 4))))
    (h3 : y3 = (max x3 (max ((x0 + x3) / 2) ((x0 + x1 + x2 + x3) / 4))))
    : |y0 - y1| + |y0 - y2| + |y0 - y3| ≤ (3 / 4) * (|x0 - x1| + |x0 - x2| + |x0 - x3|) := by
  obtain ⟨l00, l01, u0⟩ := maxBounds2 _ x0 ((x0 + x1 + x2 + x3) / 4) h0
  obtain ⟨l10, l11, l12, u1⟩ := maxBounds3 _ x1 ((x0 + x1) / 2) ((x0 + x1 + x2 + x3) / 4) h1
  obtain ⟨l20, l21, l22, u2⟩ := maxBounds3 _ x2 ((x0 + x2) / 2) ((x0 + x1 + x2 + x3) / 4) h2
  obtain ⟨l30, l31, l32, u3⟩ := maxBounds3 _ x3 ((x0 + x3) / 2) ((x0 + x1 + x2 + x3) / 4) h3
  have p0 := le_abs_self (x0 - x1)
  have n0 := neg_le_abs (x0 - x1)
  have p1 := le_abs_self (x0 - x2)
  have n1 := neg_le_abs (x0 - x2)
  have p2 := le_abs_self (x0 - x3)
  have n2 := neg_le_abs (x0 - x3)
  rcases absChoice (y0 - y1) with h01 | h01
  all_goals rcases absChoice (y0 - y2) with h02 | h02
  all_goals rcases absChoice (y0 - y3) with h03 | h03
  · rw [h01, h02, h03]
    linear_combination signed0 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 l20 l21 l22 l30 l31 l32 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed1 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed2 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 u2 l30 l31 l32 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed3 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l10 l11 l12 u2 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed4 x0 x1 x2 x3 y0 y1 y2 y3 u0 u1 l20 l21 l22 l30 l31 l32 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed5 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 u1 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed6 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 u1 u2 l30 l31 l32 p0 n0 p1 n1 p2 n2
  · rw [h01, h02, h03]
    linear_combination signed7 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 u1 u2 u3 p0 n0 p1 n1 p2 n2

/-- The ratio at the unit mass on vertex 1 is 3/4. -/
theorem starSpike :
    (|(max 0 ((0 + 1 + 0 + 0) / 4)) - (max 1 (max ((0 + 1) / 2) ((0 + 1 + 0 + 0) / 4)))| + |(max 0 ((0 + 1 + 0 + 0) / 4)) - (max 0 (max ((0 + 0) / 2) ((0 + 1 + 0 + 0) / 4)))| + |(max 0 ((0 + 1 + 0 + 0) / 4)) - (max 0 (max ((0 + 0) / 2) ((0 + 1 + 0 + 0) / 4)))| : ℝ) = 
      (3 / 4) * (|0 - 1| + |0 - 0| + |0 - 0|) := by norm_num

end SharpVariation.Four
