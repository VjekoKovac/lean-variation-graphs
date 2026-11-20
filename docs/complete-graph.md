# The complete-graph proof

Theorem 1 concerns all real functions on $K_n$, every integer $n\geq 3$, and every finite real exponent $p>0$. Its upper bound is $1-1/n$. The finite-set argument in `SharpVariation/Complete.lean` proves the upper bound already for $n\geq2$.

First take absolute values. The reverse triangle inequality shows that this can only decrease the initial variation, and all ball averages already use absolute values. Write $x_i=|f(i)|$ and $m=n^{-1}\sum_i x_i$. On a complete graph the radius-zero ball is a singleton and every positive integer radius contains all vertices. Thus the maximal function is $g_i=\max(x_i,m)$.

For a finite vertex set $S$, the helper `CompleteGraph.energy` is the **ordered** double sum $E_p(x)=\sum_{i,j\in S}|x_i-x_j|^p$. The graph energy is half of this quantity. The diagonal contributes zero, since $p>0$. Hence it suffices to prove $E_p(g)\leq (1-1/n)^p E_p(x)$, then take powers $1/p$.

## Convex exponents

For $p\geq1$, put $d_{ij}=\max(x_i-x_j,0)$. For $i$ fixed and $j\ne i$, the positive part of $g_i-g_j$ is at most $\max(x_i-m,0)$, hence at most $n^{-1}\sum_{k\ne i}d_{ik}$. Apply Jensen to the uniform average of the $n-1$ numbers $d_{ik}$, obtaining

$$
\sum_{j\ne i}\max(g_i-g_j,0)^p
\leq \left(\frac{n-1}{n}\right)^p
\sum_{j\ne i}d_{ij}^p .
$$

Sum over $i$ and multiply by two. This proves `energy_above_one`. It formalizes the proof of Theorem 1(i) in González-Riquelme and Madrid. [arXiv:2005.03146](https://arxiv.org/abs/2005.03146)

## Concave exponents

For $0<p<1$, induct on $S$, allowing the empty set and a singleton as zero-energy base cases. If no value is strictly above $m$, every $g_i=m$ and its energy vanishes. Otherwise choose a vertex $a$ of least value among those strictly above $m$. The source assigns equality to the upper block. Here vertices with value exactly $m$ belong to the lower block. Either choice yields the same maximal values.

If there are several strictly above-average vertices, the remaining ones form $H$ and the other vertices of $S\setminus\{a\}$ form $L$. Both blocks are nonempty. The average $m'$ after deletion satisfies $m'\leq m$. Raising a common floor from $m'$ to $m$ can only decrease each absolute difference. The induction hypothesis therefore bounds the energy on all pairs avoiding $a$. Its factor uses $n-1$ vertices and is at most the desired factor for $n$.

For edges incident to $a$, set $u=x_a-m$, $X_i=x_i-x_a$ on $H$, and $Y_j=x_a-x_j$ on $L$. The mean identity gives $\sum_H X_i+nu=\sum_L Y_j$, and $Y_j\geq u\geq0$, $X_i\geq0$. These are exactly the assumptions of Proposition 6. Its conclusion bounds the incident energy. The ordered energy equals the energy after deletion plus twice the incident energy. [Proof of the incident estimate](incident-estimate.md)

If $a$ is the unique vertex strictly above $m$, choose a vertex $b\ne a$ of minimum value. Put $D=x_a-x_b$. Then $x_a-m\leq(1-1/n)D$. For each vertex $i\ne a$,

$$
D^p\leq (x_a-x_i)^p+(x_i-x_b)^p .
$$

This follows from subadditivity of the power $p$. Summing over $i\ne a$ counts a subset of the undirected input edges, once each, with a zero self-term at $b$. The output energy is concentrated on the $n-1$ edges at $a$. This proves the desired estimate in the last case, following Lemma 10 of the same earlier paper.
