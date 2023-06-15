Homomorphism problems in graphs
===============================

Let G be an undirected graph whose vertices have labels.  Let H be
another graph.  A *homomorphism* from G to H is a map $f: G
\rightarrow H$ such that if $(v,w)$ is an edge of G, then $(f(v),
f(w))$ is an edge of $H$.  Note that $f$ is not necessarily injective.
We further want $f$ to be compatible with the labels of $G$.  That is,
if $\ell(v)$ denotes the label of $v$, we want $\ell(v) = \ell(w)$ if
$f(v) = f(w)$.
