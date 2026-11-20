# The incident-edge estimate

Proposition 6 of [arXiv:2603.12462](https://arxiv.org/abs/2603.12462)
controls the edges incident to the vertex removed in the induction for
Theorem 1. This note explains the proof in `SharpVariation/Analytic.lean`.

Write $k=n-r$, $l=r-1$, so $k,l\ge1$ and $n=k+l+1$. Write
$x_i\ge0$ for the differences to the higher vertices, $y_j\ge u\ge0$
for the differences to the lower vertices, and
$X=\sum_i x_i$, $\sum_j y_j=X+nu$. Throughout this estimate $0<p<1$.
The required inequality is

$$
\sum_i x_i^p+l u^p\le (1-1/n)^p\left(\sum_i x_i^p+\sum_j y_j^p\right).
$$

First set $Z=\sum_j(y_j-u)$. On $[u,u+Z]$, concavity places the function
$z\mapsto z^p$ above the chord through its two endpoint values. Summing this
lower bound gives
$$
\sum_j y_j^p\ge(l-1)u^p+(u+Z)^p=(l-1)u^p+(X+(k+2)u)^p.
$$
The case $Z=0$ follows by equality. This proves the paper's Karamata step.

For the paper's Hölder step put
$$
\delta=(n/(n-1))^p-1,\qquad q=1/(1-p),\qquad
s=\delta k^{1-p},\qquad t=(1+l\delta)/(k+2)^p.
$$
Uniform Jensen gives $\sum_i x_i^p\le k^{1-p}X^p$. The required coefficient
estimate is $s^q+t^q\le1$. In the paper $k=n-r$, $l=r-1$. For real
$2\le r\le n-1$ this left-hand side expands to the paper's $\varphi(r)$.
The theorem `paper_phi_le_one` states the bound for the expanded expression.

The Lean proof of the coefficient estimate uses
$w=p/(k+l)$ and $v=1-kw$, so $1-p\le v\le1$ and $v>0$.
By concave Bernoulli, $0\le\delta\le w\le1$. Thus $s^q=k\delta^q\le kw$.
For the second coefficient, $\log v\ge1-1/v$ gives
$$
(1-p)\log v\ge (1-p)(1-1/v)\ge v(1-1/v)=v-1.
$$
Since $k+2\ge3>e$,
$$
v\left(\frac{k+2}{v}\right)^p
=\exp((1-p)\log v+p\log(k+2))
\ge\exp(v-1+p)\ge v+p=1+lw\ge1+l\delta.
$$
This says $t\le v^{1-p}$, so $t^q\le v$. Adding gives $s^q+t^q\le1$.

Finally, with $\alpha=X$, $\beta=(k+2)u$, apply the paper's two-term Hölder
inequality with exponents $1/p$ and $q$:
$$
\alpha^p s+\beta^p t
\le (\alpha+\beta)^p(s^q+t^q)^{1-p}
\le(\alpha+\beta)^p.
$$
Consequently
$\delta\sum_i x_i^p+(1+l\delta)u^p\le(X+(k+2)u)^p$.
Combining this with concentration gives
$\sum_i x_i^p+\sum_j y_j^p\ge(1+\delta)(\sum_i x_i^p+lu^p)$,
the desired inequality.

The source proves $\varphi(r)\le1$ using convexity in $r$ and two endpoint
inequalities. The explicit coefficient bounds above replace this one part.
The concentration, uniform Jensen estimate, Hölder coefficients, Hölder step,
and incidence conclusion agree with §2.
