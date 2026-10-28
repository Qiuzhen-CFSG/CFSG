module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Scalar
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.OrderObstruction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalAmbiguity

/-!
# Remaining local A₅ construction for the short-root seed

`LocalA5.Data` states the actual Leech construction and two factor actions.
Its conditional consumer produces the scalar-class seed once the factor
automorphism fixes the shear. Both existence of this data and that identity
remain unproved here. In particular, this module does not assert
`exists_scalar_short_seed`.

The source diagonal uniqueness shortcut fails under its linear hypotheses;
`DiagonalAmbiguity` gives the explicit two alternatives. `OrderObstruction`
supplies an ambient restriction for completing the identification without
assuming faithfulness of the entire centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using 47.2 and 48.8. Final assembly belongs in this module.
-/
