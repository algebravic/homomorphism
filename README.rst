Homomorphism problems in graphs
===============================

Let G be an undirected graph whose vertices have labels.  Let H be
another graph.  A *homomorphism* from G to H is a map
$f: G \rightarrow H$ such that if $(v,w)$ is an edge of $G$, then
$(f(v), f(w))$ is an edge of $H$.  Note that $f$ is not necessarily injective.
We further want $f$ to be compatible with the labels of $G$.  That is,
if $\ell(v)$ denotes the label of $v$, we want $\ell(v) = \ell(w)$ if
$f(v) = f(w)$.  This is equivalent to choosing a labeling of the
vertices of $H$, such that $\ell(f(v)) = \ell(v)$.

Given a labeled graph $G$ and a graph $H$ we wish to find if there is
an assignment of labels to the vertices of $H$ and a labeled homomorphism
$f: G \rightarrow H$.  We do this by creating a SAT model for this.
We also exploit the special case that both $G$ and $H$ are bipartite.
In that case, if such a labeling and $f$ exists, each bipartition
of a connected component of $G$ must map to a single bipartition of
$H$.  We then encode that condition by means of new choice variables.
