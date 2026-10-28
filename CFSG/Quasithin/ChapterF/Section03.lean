module

public import Theory.Combinatorics.SimpleGraph.PathLifting

/-!
# Paths in rank-two amalgams

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, §F.3, printed pp. 269–272 (the proof of F.3.7 ends on
p. 273).

The graph-theoretic path-lifting assertion of F.3.3(1) is provided by
`SimpleGraph.BasedWalk.coveringEquiv`, `nonbacktrackingEquiv`, `allLengthsEquiv`,
and `allNonbacktrackingEquiv`. Their local-bijection hypothesis is the exact
neighbor-set property needed from the covering of coset geometries in F.3.1.
The forward map is the vertex-by-vertex map (`coveringEquiv_apply`,
`vertices_map`). These results are independent of the group or its completion.

This module currently exports that graph-theoretic ingredient. The coset-covering
construction, its equivariance and stabilizer consequences, and the polygon
results F.3.5–F.3.7 require the remaining section proofs.
-/
