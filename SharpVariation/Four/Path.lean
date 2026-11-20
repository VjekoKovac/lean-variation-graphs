module
public import SharpVariation.Four.Tools

@[expose] public section

/-! Machine-generated exact dual certificates; see `scripts/four_certificates.py`. -/
namespace SharpVariation.Four

set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

private theorem signed0 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1) / 2) ∨ y0 ≤ ((x0 + x1 + x2) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x2 + x3) / 2) ≤ y3)
    (l32 : ((x1 + x2 + x3) / 3) ≤ y3)
    (l33 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (1 : ℝ) * y0 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0 | u0
  · linear_combination u0 + l33 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination u0 + l32 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (17 / 24 : ℝ) * p1 + (1 / 24 : ℝ) * n1 + (13 / 24 : ℝ) * p2 + (5 / 24 : ℝ) * n2
  · linear_combination u0 + (2 / 3 : ℝ) * l30 + (1 / 3 : ℝ) * l33 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * p2
  · linear_combination u0 + l30 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * p2

private theorem signed1 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1) / 2) ∨ y0 ≤ ((x0 + x1 + x2) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x2 + x3) / 2) ∨ y3 ≤ ((x1 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (1 : ℝ) * y0 + (-2 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0 | u0
  all_goals rcases u3 with u3 | u3 | u3 | u3
  · linear_combination u0 + l20 + l22 + u3 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + l20 + l22 + u3 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination u0 + l21 + l22 + u3 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l22 + u3 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (11 / 24 : ℝ) * p2 + (7 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (17 / 24 : ℝ) * p1 + (1 / 24 : ℝ) * n1 + (13 / 24 : ℝ) * p2 + (5 / 24 : ℝ) * n2
  · linear_combination u0 + (3 / 2 : ℝ) * l21 + (1 / 2 : ℝ) * l22 + u3 + (11 / 16 : ℝ) * p0 + (1 / 16 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (9 / 16 : ℝ) * p2 + (3 / 16 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l20 + u3 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (17 / 24 : ℝ) * p1 + (1 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (13 / 24 : ℝ) * p2 + (5 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (7 / 24 : ℝ) * p1 + (11 / 24 : ℝ) * n1 + (1 / 12 : ℝ) * p2 + (2 / 3 : ℝ) * n2
  · linear_combination u0 + 2 * l20 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (11 / 24 : ℝ) * p1 + (7 / 24 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2
  · linear_combination u0 + 2 * l21 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (11 / 24 : ℝ) * p2 + (7 / 24 : ℝ) * n2

private theorem signed2 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1) / 2) ∨ y0 ≤ ((x0 + x1 + x2) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x2 + x3) / 2) ≤ y3)
    (l32 : ((x1 + x2 + x3) / 3) ≤ y3)
    (l33 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (1 : ℝ) * y0 + (-2 : ℝ) * y1 + (2 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0 | u0
  all_goals rcases u2 with u2 | u2 | u2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (7 / 24 : ℝ) * p2 + (11 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + (2 / 3 : ℝ) * l31 + (1 / 3 : ℝ) * l33 + (3 / 4 : ℝ) * p0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 3 : ℝ) * p2 + (5 / 12 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (7 / 24 : ℝ) * p0 + (11 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (7 / 24 : ℝ) * p0 + (11 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (7 / 24 : ℝ) * p2 + (11 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (17 / 24 : ℝ) * p1 + (1 / 24 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (7 / 24 : ℝ) * p2 + (11 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (11 / 24 : ℝ) * p0 + (7 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination u0 + (3 / 2 : ℝ) * l11 + (1 / 2 : ℝ) * l12 + 2 * u2 + l31 + (3 / 16 : ℝ) * p0 + (9 / 16 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (9 / 16 : ℝ) * p2 + (3 / 16 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (1 / 6 : ℝ) * p0 + (7 / 12 : ℝ) * n0 + (7 / 24 : ℝ) * p1 + (11 / 24 : ℝ) * n1 + (1 / 6 : ℝ) * p2 + (7 / 12 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + 2 * u2 + l31 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (11 / 24 : ℝ) * p1 + (7 / 24 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2

private theorem signed3 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1) / 2) ∨ y0 ≤ ((x0 + x1 + x2) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x2 + x3) / 2) ∨ y3 ≤ ((x1 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (1 : ℝ) * y0 + (-2 : ℝ) * y1 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0 | u0
  all_goals rcases u3 with u3 | u3 | u3 | u3
  · linear_combination u0 + l10 + l12 + u3 + (3 / 4 : ℝ) * p0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (11 / 24 : ℝ) * p1 + (7 / 24 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination u0 + l10 + l12 + u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (7 / 24 : ℝ) * p0 + (11 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l10 + u3 + (5 / 8 : ℝ) * p0 + (1 / 8 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (11 / 24 : ℝ) * p1 + (7 / 24 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination u0 + l11 + l12 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (1 / 3 : ℝ) * p0 + (5 / 12 : ℝ) * n0 + (7 / 24 : ℝ) * p1 + (11 / 24 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination u0 + 2 * l12 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination u0 + (3 / 2 : ℝ) * l11 + (1 / 2 : ℝ) * l12 + u3 + (3 / 16 : ℝ) * p0 + (9 / 16 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 16 : ℝ) * p2 + (11 / 16 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (1 / 6 : ℝ) * p0 + (7 / 12 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (1 / 12 : ℝ) * p2 + (2 / 3 : ℝ) * n2
  · linear_combination u0 + 2 * l11 + u3 + (7 / 24 : ℝ) * p0 + (11 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2

private theorem signed4 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1) / 2) ≤ y0)
    (l02 : ((x0 + x1 + x2) / 3) ≤ y0)
    (l03 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x2 + x3) / 2) ≤ y3)
    (l32 : ((x1 + x2 + x3) / 3) ≤ y3)
    (l33 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (-1 : ℝ) * y0 + (2 : ℝ) * y1 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  · linear_combination l01 + 2 * u1 + (1 / 4 : ℝ) * l30 + (3 / 4 : ℝ) * l32 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination l02 + 2 * u1 + l31 + (13 / 24 : ℝ) * p0 + (5 / 24 : ℝ) * n0 + (17 / 24 : ℝ) * p1 + (1 / 24 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination l02 + 2 * u1 + l31 + (11 / 24 : ℝ) * p0 + (7 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2

private theorem signed5 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1) / 2) ≤ y0)
    (l02 : ((x0 + x1 + x2) / 3) ≤ y0)
    (l03 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x2 + x3) / 2) ∨ y3 ≤ ((x1 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (-1 : ℝ) * y0 + (2 : ℝ) * y1 + (-2 : ℝ) * y2 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  all_goals rcases u3 with u3 | u3 | u3 | u3
  · linear_combination l01 + 2 * u1 + l20 + l22 + u3 + (3 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + l20 + l22 + u3 + (3 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + (3 / 4 : ℝ) * l20 + (1 / 4 : ℝ) * l21 + l22 + u3 + (3 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (3 / 4 : ℝ) * n0 + (5 / 8 : ℝ) * p1 + (1 / 8 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (5 / 24 : ℝ) * p1 + (13 / 24 : ℝ) * n1 + (11 / 24 : ℝ) * p2 + (7 / 24 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (1 / 3 : ℝ) * p0 + (5 / 12 : ℝ) * n0 + (7 / 24 : ℝ) * p1 + (11 / 24 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2
  · linear_combination l03 + 2 * u1 + 2 * l22 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + (1 / 2 : ℝ) * l20 + (3 / 2 : ℝ) * l22 + u3 + (3 / 16 : ℝ) * p0 + (9 / 16 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 16 : ℝ) * p2 + (11 / 16 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (1 / 8 : ℝ) * p0 + (5 / 8 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (5 / 24 : ℝ) * p2 + (13 / 24 : ℝ) * n2
  · linear_combination l01 + 2 * u1 + 2 * l22 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2

private theorem signed6 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1) / 2) ≤ y0)
    (l02 : ((x0 + x1 + x2) / 3) ≤ y0)
    (l03 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x2 + x3) / 2) ≤ y3)
    (l32 : ((x1 + x2 + x3) / 3) ≤ y3)
    (l33 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (-1 : ℝ) * y0 + (2 : ℝ) * y2 + (-1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u2 with u2 | u2 | u2
  · linear_combination l02 + 2 * u2 + l31 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (5 / 8 : ℝ) * p2 + (1 / 8 : ℝ) * n2
  · linear_combination l02 + 2 * u2 + l31 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (7 / 24 : ℝ) * p2 + (11 / 24 : ℝ) * n2
  · linear_combination l02 + 2 * u2 + l31 + (11 / 24 : ℝ) * p0 + (7 / 24 : ℝ) * n0 + (13 / 24 : ℝ) * p1 + (5 / 24 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2

private theorem signed7 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1) / 2) ≤ y0)
    (l02 : ((x0 + x1 + x2) / 3) ≤ y0)
    (l03 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x2 + x3) / 2) ∨ y3 ≤ ((x1 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x1 - x2 ≤ |x1 - x2|)
    (n1 : -(x1 - x2) ≤ |x1 - x2|)
    (p2 : x2 - x3 ≤ |x2 - x3|)
    (n2 : -(x2 - x3) ≤ |x2 - x3|)
    : (-1 : ℝ) * y0 + (1 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  rcases u3 with u3 | u3 | u3 | u3
  · linear_combination l03 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 8 : ℝ) * p1 + (5 / 8 : ℝ) * n1 + (3 / 4 : ℝ) * n2
  · linear_combination l02 + u3 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (1 / 24 : ℝ) * p1 + (17 / 24 : ℝ) * n1 + (1 / 8 : ℝ) * p2 + (5 / 8 : ℝ) * n2
  · linear_combination l03 + u3 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (7 / 24 : ℝ) * p1 + (11 / 24 : ℝ) * n1 + (1 / 3 : ℝ) * p2 + (5 / 12 : ℝ) * n2
  · linear_combination l03 + u3 + (3 / 8 : ℝ) * p0 + (3 / 8 : ℝ) * n0 + (3 / 8 : ℝ) * p1 + (3 / 8 : ℝ) * n1 + (3 / 8 : ℝ) * p2 + (3 / 8 : ℝ) * n2

/-- The real piecewise-linear upper bound for the path graph. -/
theorem pathUpper (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (h0 : y0 = (max x0 (max ((x0 + x1) / 2) (max ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4)))))
    (h1 : y1 = (max x1 (max ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4))))
    (h2 : y2 = (max x2 (max ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4))))
    (h3 : y3 = (max x3 (max ((x2 + x3) / 2) (max ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4)))))
    : |y0 - y1| + |y1 - y2| + |y2 - y3| ≤ (3 / 4) * (|x0 - x1| + |x1 - x2| + |x2 - x3|) := by
  obtain ⟨l00, l01, l02, l03, u0⟩ := maxBounds4 _ x0 ((x0 + x1) / 2) ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4) h0
  obtain ⟨l10, l11, l12, u1⟩ := maxBounds3 _ x1 ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4) h1
  obtain ⟨l20, l21, l22, u2⟩ := maxBounds3 _ x2 ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4) h2
  obtain ⟨l30, l31, l32, l33, u3⟩ := maxBounds4 _ x3 ((x2 + x3) / 2) ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4) h3
  have p0 := le_abs_self (x0 - x1)
  have n0 := neg_le_abs (x0 - x1)
  have p1 := le_abs_self (x1 - x2)
  have n1 := neg_le_abs (x1 - x2)
  have p2 := le_abs_self (x2 - x3)
  have n2 := neg_le_abs (x2 - x3)
  rcases absChoice (y0 - y1) with h01 | h01
  all_goals rcases absChoice (y1 - y2) with h12 | h12
  all_goals rcases absChoice (y2 - y3) with h23 | h23
  · rw [h01, h12, h23]
    linear_combination signed0 x0 x1 x2 x3 y0 y1 y2 y3 u0 l30 l31 l32 l33 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed1 x0 x1 x2 x3 y0 y1 y2 y3 u0 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed2 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 u2 l30 l31 l32 l33 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed3 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed4 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 l03 u1 l30 l31 l32 l33 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed5 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 l03 u1 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed6 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 l03 u2 l30 l31 l32 l33 p0 n0 p1 n1 p2 n2
  · rw [h01, h12, h23]
    linear_combination signed7 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 l03 u3 p0 n0 p1 n1 p2 n2

/-- The ratio at the unit mass on vertex 0 is 3/4. -/
theorem pathSpike :
    (|(max 1 (max ((1 + 0) / 2) (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))) - (max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| + |(max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((0 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| + |(max 0 (max ((0 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((0 + 0) / 2) (max ((0 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))))| : ℝ) = 
      (3 / 4) * (|1 - 0| + |0 - 0| + |0 - 0|) := by norm_num

end SharpVariation.Four
