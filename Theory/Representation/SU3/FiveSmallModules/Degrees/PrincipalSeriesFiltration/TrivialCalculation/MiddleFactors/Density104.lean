module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104.Polynomial
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104.Orbits

/-!
# Absolute simplicity from the degree-104 binary density certificate

A checked polynomial in the literal two binary actors gives a rank-one
operator. Checked orbit trees and two inverse matrices show that its column
and row translates span. Thus any binary subalgebra containing the actors is
the full matrix algebra. Scalar extension proves simplicity of the lower
literal quotient in any supplied `Coordinates`, over every characteristic-two
field. The construction of the canonical geometric coordinates remains with
the independent realization and middle-flag assembly.

Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- The two degree-104 binary actors generate the full matrix algebra. -/
theorem binary_density_104 : BinaryDensity factor104 := by
  intro Q hA
  exact Density104Certificate.density_of_seed_mem Q hA
    (Density104Certificate.rank_one_mem Q hA)

/-- Discharge the density premise for the lower literal quotient over any
characteristic-two coefficient field. No finite-field hypothesis is needed. -/
theorem Coordinates.lower_irreducible_104 {K : Type*} [Field K] [CharP K 2]
    (c : Coordinates K) :
    IsIrreducible (within constants c.space).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actors
    (fun j => CycleCertificate.castMatrix K (factor104 j)) c.lower c.lower_action
  exact CycleCertificate.density_cast K factor104 binary_density_104

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
