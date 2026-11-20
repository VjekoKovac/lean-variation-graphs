# The four-vertex computation

Theorem 2 of González-Riquelme, Kovač, and Madrid gives the least
constant for every connected simple graph on four vertices at exponent
one. Section 3 of the paper divides the problem into linear programs.
The Lean proof uses the same closed-ball averages and the same
piecewise-linearity. The subdivision below also covers the complete and
star graphs directly.

For a fixed graph write `xᵢ = |f(i)|`, let `aᵢᵣ` be the average of
the coordinates belonging to the radius-`r` ball centered at `i`, and let
`yᵢ = maxᵣ aᵢᵣ`. There are at most four distinct balls at a vertex.
For each undirected edge `ij`, give `yᵢ − yⱼ` its actual sign.
Expanding the absolute values expresses the output variation as
`∑ᵢ cᵢ yᵢ` with integer coefficients `cᵢ`. Several edge orientations
can give the same coefficient vector.

Fix one such vector. At each vertex with `cᵢ > 0`, choose a radius
attaining the maximum. It remains to prove a linear inequality. The
generated proof expresses the nonnegative difference between
`(3/4) ∑ᵢⱼ |xᵢ − xⱼ|` and `∑ᵢ cᵢ yᵢ` as a sum of nonnegative
rational multiples of the following inequalities.

- At a chosen positive vertex, `yᵢ ≤ aᵢᵣ` for the chosen radius.
- At a negative vertex, `aᵢᵣ ≤ yᵢ` for each radius.
- On each edge, `xᵢ − xⱼ ≤ |xᵢ − xⱼ|` and
  `−(xᵢ − xⱼ) ≤ |xᵢ − xⱼ|`.

The search script uses SciPy's linear programming interface to find the
multipliers. It reconstructs them as fractions and checks the
coefficient identities in exact arithmetic before printing Lean source.
Lean's `linear_combination` then proves each inequality from the listed
hypotheses. The build reads only the generated Lean source. The final
upper bound for signed functions follows from
`||f(i)| − |f(j)|| ≤ |f(i) − f(j)|`.

| Representative | Mask | Edges | Distinct coefficient vectors | Linear inequality certificates | Vertex of the unit mass |
| --- | ---: | --- | ---: | ---: | ---: |
| Path | 41 | 01, 12, 23 | 8 | 70 | 0 |
| Cycle | 45 | 01, 03, 12, 23 | 15 | 55 | 0 |
| Paw | 39 | 01, 02, 03, 23 | 14 | 75 | 1 |
| Diamond | 61 | 01, 03, 12, 13, 23 | 24 | 104 | 1 |
| Star | 7 | 01, 02, 03 | 8 | 74 | 1 |
| Complete | 63 | 01, 02, 03, 12, 13, 23 | 38 | 160 | 0 |

The last column gives a nonconstant function attaining equality in the
upper bound. Homogeneity allows each of the paper's scaled point masses
to be replaced by a unit mass. For example, on the path `0–1–2–3`,
the maximal function of the unit mass at 0 is `(1, 1/3, 1/4, 1/4)`.
Its edge variation is `2/3 + 1/12 = 3/4`, while the input has variation
one.

The implementation separates the scalar inequalities
(`SharpVariation/Four/Path.lean`, and analogously for the other graphs)
from the evaluation of mathematical graph balls and edge sums
(`PathGraph.lean`, etc.). The finite search in `Balls.lean` is connected
to Mathlib's shortest-walk distance. `Classification.lean` records the
labelling or separating cut for each of the 64 masks.

To regenerate the sources from the repository root, install SciPy and run

```sh
python3 scripts/four_certificates.py
python3 scripts/four_reductions.py
```

The certificate search in this development used Python 3.12.14 and SciPy 1.17.0. Other
solver versions can return different valid dual solutions.
