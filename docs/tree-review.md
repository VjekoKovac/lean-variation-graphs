# Independent AI review of the branching-tree geometry

A separate Codex AI reviewer read the level and walk argument against §5
of González-Riquelme, Kovač, and Madrid. This review checks the
mathematical reasoning behind the code. The machine checks and their
scope are recorded in `verification/`.

**Vertices and branches.** Write `t=m−1` and `d=branchLevel t`.
The level sequence in the code starts with ℓ₁=2, so `d=ℓ_m` and the
tree has height `H=2d+1=ℓ_{m+1}`. At level `h` an integer label lies
in `[0,k^{e(h)})`. Its parent label is obtained by taking the remainder
modulo `k^{e(h−1)}`. Increasing the exponent by one creates exactly
`k` choices of child. At the final level it increases by two, giving
`k²` leaves for each last-level parent. Successive remainders preserve
the oldest branch choices because the corresponding powers of `k`
divide one another. Every nonroot vertex has a unique parent, and the
root has one neighbor. The existential theorem asks for a connected
simple graph. The supplementary theorem `PaperTree.tree_isTree` also
proves that this graph is a tree.

**Walks and the small ball.** Each edge changes depth by one. For a walk
from a vertex at depth `u` to a vertex at depth `v`, consider an
intermediate vertex of depth `j`. The two pieces of the walk contribute
at least `u−j` and `v−j` to its length `L`. Thus if
`L+2a ≤ u+v+1`, then `2a ≤ 2j+1`, and `a ≤ j` by integrality.
Thus every vertex on the walk has depth at least `a`. Along each edge, the label
modulo `k^{e(a)}` is therefore unchanged. The induction in
`Geometry.walk_prefix` proves this for arbitrary walks, including paths
which turn more than once.

The radius from a distinguished vertex `b` at depth `d` to the root
is `d`. A vertex at depth `h` in that ball has `h ≤ 2d < H`.
Take `a=⌊h/2⌋`. The walk condition follows from `L ≤ d`. All
reachable labels in this level consequently have the same remainder
modulo `k^{e(a)}`. The gaps between branching levels give
`e(h) ≤ e(a)+1`, including levels before the first branch. There are
at most `k` labels with that remainder. Summing over the levels gives
a bound of the form `C_m k`, with no dependence of `C_m` on `k`.

**The neighboring vertex and the large ball.** Each `b` has a successor
`w` at depth `d+1`, before the final branch. Keeping the same prefix
allows `k²` distinct leaves at depth `H`, each at distance at most
`H−(d+1)=d` from `w`. Its ball reaching the root has radius `d+1`
and contains all these leaves. For a point mass at the root, the
maximal average is the reciprocal of the size of the *first* ball
reaching the root: smaller balls have zero numerator; larger balls
have the same numerator and at least as large a denominator. The
`k^m` vertices on the distinguished level give distinct edges. Both
orientations occur in the energy sum, exactly canceling its factor of
one half.

The level indexing, the exponent jump at the terminal leaves, both
ball bounds, and the direction of the reciprocal inequalities agree
with the paper. This review is AI-generated and does not record approval
by the authors.
