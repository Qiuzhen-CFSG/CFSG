module

public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Isometry
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.GeneratorCoordinates
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.GeneratorCompatibility

/-!
# The source Golay–Leech coordinate comparison

The fixed `sourceLatticeComparison` sends `(v,J+Golay)` to the class of
`2 1_v + 4 1_J - |J| 1_X` in the actual ATLAS Leech lattice modulo twice
itself. The representative identities prove the source's twisted addition
and quadratic form. The composite `sourceQ1QuotientLatticeIsometry`
identifies the actual central quotient of `Q1/⟨k1⟩` with this Leech quotient;
`sourceQ1LatticeHom` is the source surjection with kernel `⟨z1,k1⟩`.

The comparison intertwines actual triality conjugations by `ψ₁(d)`, `ψ₂(d)`
and every standard `ψ₁(α)` with, respectively, the identity, the Leech sign
isometry and the Leech coordinate permutation. These equations hold on all
coordinates and through both actual quotient maps. The fixed real comparison
`naturalLeechComparison` intertwines the same isometries with the genuine
signed halfspace transports. Permutations move basis labels forward and
reindex coordinate functions by the inverse. Full `N1`-equivariance is
assembled from these generator equations by `LocalC`.

Source: Aschbacher, *Sporadic Groups*, Sections 23.8–23.10, pp. 119–121,
and Lemma 27.2 and the subsequent generator comparison, pp. 144–148.
The Golay and Leech models are the attributed ATLAS ports.
-/
