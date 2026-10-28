module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Flag
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras.Fifteen
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras.FortyFive
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras.Six

/-!
# Full matrix algebras of the three natural induced Mathieu factors

The fixed factor matrices of dimensions 15, 45 and 6 generate their full
matrix algebras over the actual four-element field. Each calculation uses a
checked rank-one element, two recursively generated spanning orbits, and
checked inverse matrices. All numerical identities are kernel checked using
sound packed F₄ arithmetic; no irreducibility oracle is used.

This density statement is independent of quotient coordinates. The final
consumer applies it to each literal successive quotient when its equivariant
coordinate isomorphism is supplied. The independent coordinate producer
must still construct those isomorphisms to complete the filtration.

Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7. The supplied candidate
certificates and original ATLAS provenance are documented in
`NaturalFiltration/source/README.md`.
-/

public section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration

/-- All three fixed pairs generate the full F₄ matrix algebra. -/
theorem factorDensity (s : Fin 3) : FactorDensity s := by
  fin_cases s
  · exact FactorAlgebraCertificate.Fifteen.density
  · exact FactorAlgebraCertificate.FortyFive.density
  · exact FactorAlgebraCertificate.Six.density

/-- Equivariant coordinates on a literal factor now suffice for irreducibility. -/
theorem factor_irreducible (s : Fin 3) (c : FactorCoordinates s) :
    (factorRepresentation s).IsIrreducible :=
  factor_irreducible_of_coordinates s c (factorDensity s)

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
