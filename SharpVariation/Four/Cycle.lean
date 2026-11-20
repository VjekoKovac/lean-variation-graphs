module
public import SharpVariation.Four.Tools

@[expose] public section

/-! Machine-generated exact dual certificates; see `scripts/four_certificates.py`. -/
namespace SharpVariation.Four

set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

private theorem signed0 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x3) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x2 + x3) / 3) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y0 + (-2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0
  · linear_combination 2 * u0 + 2 * l31 + (3 / 4 : ℝ) * p0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l30 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u0 + 2 * l30 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed1 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x3) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y0 + (-2 : ℝ) * y2 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0
  · linear_combination 2 * u0 + 2 * l22 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (1 / 4 : ℝ) * p3 + (1 / 2 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l21 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l21 + (3 / 4 : ℝ) * p0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (2 / 3 : ℝ) * p2 + (1 / 12 : ℝ) * n2 + (7 / 12 : ℝ) * p3 + (1 / 6 : ℝ) * n3

private theorem signed2 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x3) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x2 + x3) / 3) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y0 + (-2 : ℝ) * y1 + (2 : ℝ) * y2 + (-2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0
  all_goals rcases u2 with u2 | u2 | u2
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (3 / 4 : ℝ) * p0 + (7 / 12 : ℝ) * p1 + (1 / 6 : ℝ) * n1 + (2 / 3 : ℝ) * p2 + (1 / 12 : ℝ) * n2 + (1 / 4 : ℝ) * p3 + (1 / 2 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (1 / 6 : ℝ) * p1 + (7 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (1 / 3 : ℝ) * p3 + (5 / 12 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (1 / 6 : ℝ) * p2 + (7 / 12 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (1 / 3 : ℝ) * p0 + (5 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2 + (1 / 2 : ℝ) * p3 + (1 / 4 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + 2 * u2 + 2 * l31 + (7 / 12 : ℝ) * p0 + (1 / 6 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (7 / 12 : ℝ) * p3 + (1 / 6 : ℝ) * n3

private theorem signed3 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u0 : y0 ≤ x0 ∨ y0 ≤ ((x0 + x1 + x3) / 3) ∨ y0 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y0 + (-2 : ℝ) * y1 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u0 with u0 | u0 | u0
  · linear_combination 2 * u0 + 2 * l11 + (3 / 4 : ℝ) * p0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (1 / 12 : ℝ) * p3 + (2 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u0 + 2 * l11 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2 + (1 / 2 : ℝ) * p3 + (1 / 4 : ℝ) * n3

private theorem signed4 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (0 : ℝ) ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  linear_combination (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (3 / 4 : ℝ) * p3

private theorem signed5 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y2 + (2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u3 with u3 | u3 | u3
  · linear_combination 2 * l21 + 2 * u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (1 / 3 : ℝ) * p2 + (5 / 12 : ℝ) * n2 + (3 / 4 : ℝ) * n3
  · linear_combination 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (2 / 3 : ℝ) * p2 + (1 / 12 : ℝ) * n2 + (7 / 12 : ℝ) * p3 + (1 / 6 : ℝ) * n3

private theorem signed6 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y1 + (2 : ℝ) * y2 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u2 with u2 | u2 | u2
  · linear_combination 2 * l11 + 2 * u2 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 12 : ℝ) * p2 + (2 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l11 + 2 * u2 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * l11 + 2 * u2 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2 + (1 / 2 : ℝ) * p3 + (1 / 4 : ℝ) * n3

private theorem signed7 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l10 : x1 ≤ y1)
    (l11 : ((x0 + x1 + x2) / 3) ≤ y1)
    (l12 : ((x0 + x1 + x2 + x3) / 4) ≤ y1)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y1 + (2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u3 with u3 | u3 | u3
  · linear_combination 2 * l12 + 2 * u3 + (1 / 2 : ℝ) * p0 + (1 / 4 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2 + (3 / 4 : ℝ) * n3
  · linear_combination 2 * l11 + 2 * u3 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * l11 + 2 * u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2 + (1 / 2 : ℝ) * p3 + (1 / 4 : ℝ) * n3

private theorem signed8 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x2 + x3) / 3) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y1 + (-2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  · linear_combination 2 * u1 + 2 * l32 + (3 / 4 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * p3 + (1 / 4 : ℝ) * n3
  · linear_combination 2 * u1 + (5 / 4 : ℝ) * l30 + (3 / 4 : ℝ) * l31 + (5 / 24 : ℝ) * p0 + (13 / 24 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (13 / 24 : ℝ) * p2 + (5 / 24 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u1 + 2 * l30 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed9 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y1 + (-2 : ℝ) * y2 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  · linear_combination 2 * u1 + 2 * l21 + (1 / 12 : ℝ) * p0 + (2 / 3 : ℝ) * n0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * u1 + 2 * l21 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u1 + 2 * l21 + (3 / 4 : ℝ) * p0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (2 / 3 : ℝ) * p2 + (1 / 12 : ℝ) * n2 + (7 / 12 : ℝ) * p3 + (1 / 6 : ℝ) * n3

private theorem signed10 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l30 : x3 ≤ y3)
    (l31 : ((x0 + x2 + x3) / 3) ≤ y3)
    (l32 : ((x0 + x1 + x2 + x3) / 4) ≤ y3)
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (2 : ℝ) * y2 + (-2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u2 with u2 | u2 | u2
  · linear_combination 2 * u2 + 2 * l31 + (1 / 12 : ℝ) * p0 + (2 / 3 : ℝ) * n0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (1 / 12 : ℝ) * p2 + (2 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u2 + 2 * l30 + (1 / 12 : ℝ) * p0 + (2 / 3 : ℝ) * n0 + (2 / 3 : ℝ) * p1 + (1 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * u2 + 2 * l30 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (3 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed11 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x3) / 3) ≤ y0)
    (l02 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y0 + (2 : ℝ) * y1 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  · linear_combination 2 * l01 + 2 * u1 + (1 / 12 : ℝ) * p0 + (2 / 3 : ℝ) * n0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u1 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u1 + (7 / 12 : ℝ) * p0 + (1 / 6 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed12 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x3) / 3) ≤ y0)
    (l02 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u1 : y1 ≤ x1 ∨ y1 ≤ ((x0 + x1 + x2) / 3) ∨ y1 ≤ ((x0 + x1 + x2 + x3) / 4))
    (l20 : x2 ≤ y2)
    (l21 : ((x1 + x2 + x3) / 3) ≤ y2)
    (l22 : ((x0 + x1 + x2 + x3) / 4) ≤ y2)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y0 + (2 : ℝ) * y1 + (-2 : ℝ) * y2 + (2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u1 with u1 | u1 | u1
  all_goals rcases u3 with u3 | u3 | u3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (1 / 6 : ℝ) * p0 + (7 / 12 : ℝ) * n0 + (1 / 2 : ℝ) * p1 + (1 / 4 : ℝ) * n1 + (3 / 4 : ℝ) * p2 + (2 / 3 : ℝ) * p3 + (1 / 12 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (5 / 12 : ℝ) * p3 + (1 / 3 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (1 / 3 : ℝ) * p1 + (5 / 12 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (7 / 12 : ℝ) * p0 + (1 / 6 : ℝ) * n0 + (5 / 12 : ℝ) * p1 + (1 / 3 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (2 / 3 : ℝ) * p0 + (1 / 12 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (1 / 4 : ℝ) * p2 + (1 / 2 : ℝ) * n2 + (1 / 6 : ℝ) * p3 + (7 / 12 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (1 / 3 : ℝ) * p2 + (5 / 12 : ℝ) * n2 + (7 / 12 : ℝ) * p3 + (1 / 6 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u1 + 2 * l21 + 2 * u3 + (3 / 4 : ℝ) * p0 + (1 / 6 : ℝ) * p1 + (7 / 12 : ℝ) * n1 + (7 / 12 : ℝ) * p2 + (1 / 6 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed13 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x3) / 3) ≤ y0)
    (l02 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u2 : y2 ≤ x2 ∨ y2 ≤ ((x1 + x2 + x3) / 3) ∨ y2 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y0 + (2 : ℝ) * y2 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u2 with u2 | u2 | u2
  · linear_combination 2 * l02 + 2 * u2 + (1 / 4 : ℝ) * p0 + (1 / 2 : ℝ) * n0 + (1 / 4 : ℝ) * p1 + (1 / 2 : ℝ) * n1 + (3 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u2 + (5 / 12 : ℝ) * p0 + (1 / 3 : ℝ) * n0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u2 + (7 / 12 : ℝ) * p0 + (1 / 6 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

private theorem signed14 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (l00 : x0 ≤ y0)
    (l01 : ((x0 + x1 + x3) / 3) ≤ y0)
    (l02 : ((x0 + x1 + x2 + x3) / 4) ≤ y0)
    (u3 : y3 ≤ x3 ∨ y3 ≤ ((x0 + x2 + x3) / 3) ∨ y3 ≤ ((x0 + x1 + x2 + x3) / 4))
    (p0 : x0 - x1 ≤ |x0 - x1|)
    (n0 : -(x0 - x1) ≤ |x0 - x1|)
    (p1 : x0 - x3 ≤ |x0 - x3|)
    (n1 : -(x0 - x3) ≤ |x0 - x3|)
    (p2 : x1 - x2 ≤ |x1 - x2|)
    (n2 : -(x1 - x2) ≤ |x1 - x2|)
    (p3 : x2 - x3 ≤ |x2 - x3|)
    (n3 : -(x2 - x3) ≤ |x2 - x3|)
    : (-2 : ℝ) * y0 + (2 : ℝ) * y3 ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  rcases u3 with u3 | u3 | u3
  · linear_combination 2 * l01 + 2 * u3 + (1 / 3 : ℝ) * p0 + (5 / 12 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (3 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * n3
  · linear_combination 2 * l01 + 2 * u3 + (3 / 4 : ℝ) * p0 + (3 / 4 : ℝ) * n1 + (5 / 12 : ℝ) * p2 + (1 / 3 : ℝ) * n2 + (3 / 4 : ℝ) * p3
  · linear_combination 2 * l01 + 2 * u3 + (7 / 12 : ℝ) * p0 + (1 / 6 : ℝ) * n0 + (1 / 12 : ℝ) * p1 + (2 / 3 : ℝ) * n1 + (1 / 2 : ℝ) * p2 + (1 / 4 : ℝ) * n2 + (3 / 4 : ℝ) * p3

/-- The real piecewise-linear upper bound for the cycle graph. -/
theorem cycleUpper (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)
    (h0 : y0 = (max x0 (max ((x0 + x1 + x3) / 3) ((x0 + x1 + x2 + x3) / 4))))
    (h1 : y1 = (max x1 (max ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4))))
    (h2 : y2 = (max x2 (max ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4))))
    (h3 : y3 = (max x3 (max ((x0 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4))))
    : |y0 - y1| + |y0 - y3| + |y1 - y2| + |y2 - y3| ≤ (3 / 4) * (|x0 - x1| + |x0 - x3| + |x1 - x2| + |x2 - x3|) := by
  obtain ⟨l00, l01, l02, u0⟩ := maxBounds3 _ x0 ((x0 + x1 + x3) / 3) ((x0 + x1 + x2 + x3) / 4) h0
  obtain ⟨l10, l11, l12, u1⟩ := maxBounds3 _ x1 ((x0 + x1 + x2) / 3) ((x0 + x1 + x2 + x3) / 4) h1
  obtain ⟨l20, l21, l22, u2⟩ := maxBounds3 _ x2 ((x1 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4) h2
  obtain ⟨l30, l31, l32, u3⟩ := maxBounds3 _ x3 ((x0 + x2 + x3) / 3) ((x0 + x1 + x2 + x3) / 4) h3
  have p0 := le_abs_self (x0 - x1)
  have n0 := neg_le_abs (x0 - x1)
  have p1 := le_abs_self (x0 - x3)
  have n1 := neg_le_abs (x0 - x3)
  have p2 := le_abs_self (x1 - x2)
  have n2 := neg_le_abs (x1 - x2)
  have p3 := le_abs_self (x2 - x3)
  have n3 := neg_le_abs (x2 - x3)
  rcases absChoice (y0 - y1) with h01 | h01
  all_goals rcases absChoice (y0 - y3) with h03 | h03
  all_goals rcases absChoice (y1 - y2) with h12 | h12
  all_goals rcases absChoice (y2 - y3) with h23 | h23
  · rw [h01, h03, h12, h23]
    linear_combination signed0 x0 x1 x2 x3 y0 y1 y2 y3 u0 l30 l31 l32 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed1 x0 x1 x2 x3 y0 y1 y2 y3 u0 l20 l21 l22 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed2 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 u2 l30 l31 l32 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed3 x0 x1 x2 x3 y0 y1 y2 y3 u0 l10 l11 l12 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed4 x0 x1 x2 x3 y0 y1 y2 y3 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed5 x0 x1 x2 x3 y0 y1 y2 y3 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed6 x0 x1 x2 x3 y0 y1 y2 y3 l10 l11 l12 u2 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed7 x0 x1 x2 x3 y0 y1 y2 y3 l10 l11 l12 u3 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed8 x0 x1 x2 x3 y0 y1 y2 y3 u1 l30 l31 l32 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed9 x0 x1 x2 x3 y0 y1 y2 y3 u1 l20 l21 l22 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed10 x0 x1 x2 x3 y0 y1 y2 y3 u2 l30 l31 l32 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed4 x0 x1 x2 x3 y0 y1 y2 y3 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed11 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 u1 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed12 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 u1 l20 l21 l22 u3 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed13 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 u2 p0 n0 p1 n1 p2 n2 p3 n3
  · rw [h01, h03, h12, h23]
    linear_combination signed14 x0 x1 x2 x3 y0 y1 y2 y3 l00 l01 l02 u3 p0 n0 p1 n1 p2 n2 p3 n3

/-- The ratio at the unit mass on vertex 0 is 3/4. -/
theorem cycleSpike :
    (|(max 1 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| + |(max 1 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| + |(max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((0 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| + |(max 0 (max ((0 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4))) - (max 0 (max ((1 + 0 + 0) / 3) ((1 + 0 + 0 + 0) / 4)))| : ℝ) = 
      (3 / 4) * (|1 - 0| + |1 - 0| + |0 - 0| + |0 - 0|) := by norm_num

end SharpVariation.Four
