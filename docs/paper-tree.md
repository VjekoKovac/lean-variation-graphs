# The tree with arbitrarily large constants

Fix real numbers `p > 0` and `C > 0`. Section 5 of the paper constructs a
finite connected graph and an input for which the output variation is
strictly greater than `C` times the input variation. The input will be one
at the root and zero elsewhere. The root has only one neighbor, so its
input variation is exactly one for every positive real exponent.

## Reading the construction

Choose an integer $m>p$. The code uses the index $t=m-1$. It takes $t$ to
be any natural number larger than $p$, so in particular $t+1>p$. Fix an
integer branching number $k\ge2$ for now. Its size will be chosen in the
last step.

The paper starts with $\ell_0=1$ and
$\ell_i=i+\sum_{j<i}\ell_j$ for $i\ge1$. Thus $\ell_1=2$.
Subtracting consecutive formulas gives $\ell_{i+1}=2\ell_i+1$ for
$i\ge1$. The code begins its numbering at the first branching child.
Consequently `branchLevel s` equals $\ell_{s+1}=3\cdot2^s-1$. Set
$d=\ell_m$ and $H=\ell_{m+1}=2d+1$. The vertices have depths
$0,\ldots,H$ inclusive.

| Depth | Number of vertices | Meaning |
|---|---:|---|
| $0$ and $1$ | $1$ at each depth | The root and its unique neighbor |
| $\ell_j$ through $\ell_{j+1}-1$, for $1\le j\le m$ | $k^j$ at each depth | Each new ordinary branching contributes one choice among $k$ children |
| $H=\ell_{m+1}$ | $k^{m+2}$ | Each of the $k^m$ parents at depth $H-1$ has $k^2$ leaves |

A vertex is a depth $h$ and an integer label from $0$ through
$k^{e(h)}-1$. The exponent $e(h)$ counts the ordinary branching steps
up to $h$, with an extra two digits at the final depth. The vertex type
in Lean is a dependent pair whose second component belongs to
`Fin (k ^ exponent t h)`. It therefore has precisely the number of
labels shown in the table. At adjacent depths, reducing the deeper
label modulo the shallower level's number of labels gives its parent.
In base $k$, the lowest digits record the earliest branch choices.
Keeping the same integer and reducing it at every intervening depth
constructs a vertical walk. Depth changes by one at each edge, so the
distance of a vertex from the root equals its depth.

The supplementary theorem `SharpVariation.PaperTree.tree_isTree` in
`TreeStructure.lean` also proves acyclicity. A cycle has a vertex of
maximum depth. Its preceding and following vertices would both have
to be its parent, whereas those two neighbors on a simple cycle are
distinct.

## Two balls on the same stalk

At depth $d$ there are $k^m$ vertices $b_i$, indexed by
$i=0,\ldots,k^m-1$. Let $w_i$ be the unique child of $b_i$. This child
has depth $d+1$ and the same label $i$.

**The ball around $b_i$.** Suppose a vertex of depth $h$ lies in
$B(b_i,d)$. Then $h\le 2d$, so it lies strictly above the terminal leaves.
Put $a=\lfloor h/2\rfloor$. Any walk from depth $d$ to depth $h$ that
visits depth $s<a$ has length at least
$(d-s)+(h-s)=d+h-2s>d$. Thus a shortest walk in this ball keeps depths
at least $a$, and its labels agree modulo $k^{e(a)}$. This fixes the
remainder of the endpoint's label from its depth and the center label.

Two consecutive branching depths satisfy $\ell_{j+1}=2\ell_j+1$.
It follows that between depths $a$ and $h$ there can be at most one
additional branching, meaning $e(h)\le e(a)+1$. Among the $k^{e(h)}$
labels, at most $k$ have the required remainder. Lean proves an injection by
storing the vertex's depth and the quotient of its label by
$k^{e(a)}$. The quotient is smaller than $k$. Equal codes have equal
depths, quotients and remainders, so they recover the same vertex.
The pair of codes ranges over exactly $(H+1)k$ possibilities. In
particular the proof takes the explicit constant $C_m=H+1$ and obtains
$|B(b_i,d)|\le C_m k$. This constant depends only on $m$.

**The ball around $w_i$.** The labels
$i+k^m j$, for $0\le j<k^2$, give $k^2$ distinct leaves below $w_i$.
Each leaf is $H-(d+1)=d$ edges below $w_i$ and therefore belongs to
$B(w_i,d+1)$. Hence $|B(w_i,d+1)|\ge k^2$.

## From ball counts to variation

Let $v$ be the root and $f=\mathbf 1_{\{v\}}$. At a vertex $u$, balls
of radius smaller than $d(u,v)$ have zero average. Every larger ball
contains $v$ and has numerator one. Its denominator increases with
radius, so $M f(u)$ is exactly the reciprocal of the cardinality of
the first ball reaching $v$. The two bounds above give
$M f(b_i)\ge1/(C_m k)$ and $M f(w_i)\le1/k^2$.

Take $k$ large enough that $k\ge2C_m$. Each of the $k^m$ distinct edges
$b_iw_i$ contributes at least $(1/(C_m k)-1/k^2)^p$ to the output
energy. Lean counts both orientations and divides by two, as in the
definition of variation. Consequently

$$
\operatorname{Var}_p(M f)^p
\;\ge\; k^m \left(\frac1{C_m k}-\frac1{k^2}\right)^p
\;\ge\; \frac{k^{m-p}}{(2C_m)^p}.
$$

The exponent $m-p$ is positive even when $p$ is nonintegral or less
than one. The Archimedean property gives an integer $k$ making the last
quantity strictly greater than $C^p$. Taking the positive $p$-th root
and using $\operatorname{Var}_p(f)=1$ proves the requested strict
inequality.

## Lean reading order

Names in the first four rows live in `SharpVariation.PaperTree`. The
`Geometry` prefix denotes its geometry subnamespace.

| File | Declarations to look for | Mathematical role |
|---|---|---|
| `PaperTreeLevels.lean` | `branchLevel`, `level_closed`, `exponent`, `exponent_half` | Branching depths, number of digits, and their growth on doubling depth |
| `PaperTreeGeometry.lean` | `Geometry.Vertex`, `Geometry.graph`, `Geometry.vertical_walk`, `Geometry.walk_prefix` | Vertices, edges, vertical walks and preservation of the low digits |
| `PaperTreeLeaves.lean` | `root_neighbor`, `dist_center_root`, `dist_child_root`, `le_child_card` | Root degree, exact radii and the $k^2$ distinct leaves |
| `PaperTreeCenters.lean` | `center_card_le` | Upper bound $(H+1)k$ for the ball around each distinguished center |
| `TreeDirac.lean` | `SharpVariation.TreeExample.maximal_dirac`, `SharpVariation.TreeExample.tree_dirac_energy` | The exact maximal average and the sum over distinct edges |
| `TreeGrowth.lean` | `SharpVariation.tree_growth` | Choice of an integer $k$ giving a strict inequality |
| `PaperTree.lean`, `Solution.lean` | `SharpVariation.PaperTree.large_witness`, `SharpVariation.largeConst` | Assembly of the existential theorem |

The construction is due to González-Riquelme, Kovač and Madrid in
[*Sharp variational inequalities for the Hardy–Littlewood maximal operator
on finite undirected graphs*, §5](https://arxiv.org/html/2603.12462v1).
