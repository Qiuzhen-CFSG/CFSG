module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.Coordinates
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Scalars
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Flag
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.FactorAlgebras
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.QuotientCoordinates

/-!
# Assembling the natural induced-module filtration

Equivariant coordinates on the three literal field quotients, together with
full matrix-algebra certificates for their fixed generator pairs, give an
actual field filtration. The proved central omega action then restricts that
filtration to binary simple factors of dimensions 30, 90 and 12.

The checked quotient coordinates identify the invariant flag of field dimensions
0, 15, 60 and 66 with the saved adapted basis. The checked rank-one and orbit
certificates prove simplicity of all three literal quotients. Together they
discharge the coordinate and density inputs of the assembly below, giving
`natural_factorDegreeFiltration` without additional premises. The induced-quotient
exclusion belongs to the parent `InducedQuotients` module.
Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
open Representation NaturalFiltration

/-- Apply both concrete field certificates to the actual induced binary action. -/
theorem natural_factorDegreeFiltration_of_coordinates
    (c : ∀ s, FactorCoordinates s) (h : ∀ s, FactorDensity s) :
    FactorDegreeFiltration ({12, 30, 90} : Set ℕ)
      (representation Representation.SL3FourLocalCatalogue.Constituent.natural) :=
  natural_filtration_of_field (field_filtration_of_coordinates c h)

/-- The natural induced point module has an actual invariant filtration with
simple binary factors of degrees 30, 90 and 12. This supplies the natural branch
of the parent's induced-quotient exclusion. -/
theorem natural_factorDegreeFiltration :
    FactorDegreeFiltration ({12, 30, 90} : Set ℕ)
      (representation Representation.SL3FourLocalCatalogue.Constituent.natural) :=
  natural_factorDegreeFiltration_of_coordinates
    (fun s => (nonempty_factorCoordinates s).some) factorDensity

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
