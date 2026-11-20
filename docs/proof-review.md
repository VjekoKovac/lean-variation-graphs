# Independent AI review of the complete-graph argument

An AI reviewer who did not write `SharpVariation/Complete.lean` or
`SharpVariation/Graph.lean` read their definitions and arguments against
Theorem 1 and §2 of [arXiv:2603.12462v1](https://arxiv.org/html/2603.12462v1).
This is a mathematical and clarity review. The verification transcript records
the separate mechanical checks. The reviewer did write `Analytic.lean`;
another AI reviewer independently evaluated its scalar argument.

* **Graph convention.** A connected finite simple graph supplies the shortest-path
  metric used in the statement. The finite supremum includes the singleton ball
  and all sufficiently large balls. For an arbitrary real radius $r\ge0$, taking
  its integer part leaves every ball unchanged since the distances are integers.
  In `ballAverage_le_maximal` the bound on the length of a simple shortest path
  explains why the finite range captures all integer radii. The sum over ordered
  adjacent pairs divided by two counts each undirected edge once. The proof
  comparing $|f|$ with $f$ uses the reverse triangle inequality on each edge.
* **Convex exponents.** For $p\ge1$ the source cites González-Riquelme and
  Madrid. The Lean file gives an actual argument. Set $g_i=\max(f_i,m)$ and
  $d_j=(f_i-f_j)_+$ with $i$ fixed. Each $(g_i-g_j)_+$ is at most
  $\sum_{k\ne i}d_k/n$. Jensen on those $n-1$ terms bounds the sum of
  $p$th powers in that row by $((n-1)/n)^p\sum_{j\ne i}d_j^p$.
  Summing over $i$ gives the desired ordered-pair estimate, since the two
  orientations together recover the absolute edge difference.
  The convex proof includes $p=1$. [Earlier paper](https://arxiv.org/abs/2005.03146)
* **Subunit exponents.** For $0<p<1$ the proof deletes the least value strictly
  above the mean. The paper sorts the list and takes the least value greater
  than or equal to the mean. Assigning values equal to the mean to the lower
  set is valid. Their maximal value remains the mean, and their gap from the
  pivot equals $u$, allowed in Proposition 6. If no value exceeds the mean, the
  thresholded function is constant. Otherwise there is at least one value at
  most the mean. Erasing the pivot decreases the mean, so thresholding the
  remaining pairs at the original mean gives no larger differences than
  thresholding them at their own mean. The ordered-pair sum splits into the
  remaining sum plus twice the deleted row, also when other vertices tie the
  pivot.
* **Endpoints of induction.** Empty and singleton vertex sets have zero pair
  energy. This proves the required induction bases internally, including the
  paper's cited three-vertex base. If only the pivot $a$ lies above the mean,
  take a minimum $b$ among the other vertices. For each $i\ne a$,
  $(f_a-f_b)^p\le |f_a-f_i|^p+|f_i-f_b|^p$. Summing counts the star at $a$
  and the residual star at $b$ once each. This gives the needed estimate,
  since $f_a-m\le(1-1/n)(f_a-f_b)$. Positivity of $p$ justifies both the
  vanishing diagonal and taking the $p$th root at the end.
* **Induction dependency.** The checked scalar estimate `incident_subunit` is
  invoked directly by `energy_below_one`. The induction does not require a
  hypothesis supplying Proposition 6. The set sizes $k=n-r$ and $l=r-1$ are both positive in this
  branch and the balance $\sum x_i+nu=\sum y_j$ follows from the mean.
  The [incident-edge note](incident-estimate.md) explains the coefficient
  bounds used to prove the source's Hölder condition on its full interval.
* **Public theorem.** The solution applies `complete_sum_le` to $|f|$,
  identifies its thresholded mean with the graph maximal function via
  `maximal_top`, accounts for the factor $1/2$ using `energy_top`, and invokes
  `variation_le_of_energy_le`. No smoothness, nonnegativity, or nonconstancy
  is imposed on the input function.

The reviewer found no mathematical gap in these arguments. This review does
not supply a human author sign-off or independently check the four-vertex
certificate files or the large-constant construction.
