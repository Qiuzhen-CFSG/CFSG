module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Action
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density20
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CosetCardinality

/-!
# The two middle simple factors of the canonical SU₃(5) coset module

Binary matrix-algebra density survives arbitrary characteristic-two scalar
extension. An equivariant coordinate isomorphism therefore proves simplicity
of each literal quotient, while its target gives dimension 104 or 20.
The checked coset realization and the literal Borel index construct the
105-dimensional invariant subspace between constants and augmentation.
The two checked binary density certificates discharge the simplicity inputs,
giving `canonical_middle_flags` over every finite characteristic-two field.

Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

namespace MiddleFactors
universe v
variable {K : Type v} [Field K] [CharP K 2]

/-- Binary density proves simplicity of the lower literal quotient over K. -/
theorem Coordinates.lower_irreducible (c : Coordinates K) (h : BinaryDensity factor104) :
    IsIrreducible (within constants c.space).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actors
    (fun j => CycleCertificate.castMatrix K (factor104 j)) c.lower c.lower_action
  exact CycleCertificate.density_cast K factor104 h

/-- The upper quotient is simple over the same K, without a splitting-field assumption. -/
theorem Coordinates.upper_irreducible (c : Coordinates K) (h : BinaryDensity factor20) :
    IsIrreducible (within c.space augmentationKernel).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actors
    (fun j => CycleCertificate.castMatrix K (factor20 j)) c.upper c.upper_action
  exact CycleCertificate.density_cast K factor20 h

theorem Coordinates.lower_finrank (c : Coordinates K) :
    Module.finrank K (c.space.toSubmodule ⧸ (within constants c.space).toSubmodule) = 104 := by
  rw [c.lower.finrank_eq]
  simp

theorem Coordinates.upper_finrank (c : Coordinates K) :
    Module.finrank K (augmentationKernel.toSubmodule ⧸
      (within c.space augmentationKernel).toSubmodule) = 20 := by
  rw [c.upper.finrank_eq]
  simp

/-- The constructed intermediate subspace has the expected dimension 105. -/
theorem Coordinates.space_finrank (c : Coordinates K) :
    Module.finrank K c.space.toSubmodule = 105 := by
  have h := (within constants c.space).toSubmodule.finrank_quotient_add_finrank
  rw [c.lower_finrank, ← (withinEquiv constants c.space c.constants_le).finrank_eq,
    finrank_constants] at h
  exact h.symm

/-- Consume all three independent mathematical inputs on the actual coset module. -/
theorem Coordinates.middleFlag (c : Coordinates K)
    (h104 : BinaryDensity factor104) (h20 : BinaryDensity factor20) :
    MiddleFlag (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints) := by
  refine ⟨c.space, c.constants_le, c.le_augmentation,
    c.lower_irreducible h104, c.upper_irreducible h20, ?_, ?_⟩
  · rw [c.lower_finrank]
    simp
  · rw [c.upper_finrank]
    simp

end MiddleFactors

universe v
/-- Conditional assembly only: the canonical coordinates and both binary
density certificates must be supplied before the source flag is established. -/
theorem canonical_middle_flags_of_coordinates_and_density
    (hc : MiddleFactors.CanonicalCoordinates.{v})
    (h104 : MiddleFactors.BinaryDensity MiddleFactors.factor104)
    (h20 : MiddleFactors.BinaryDensity MiddleFactors.factor20) : CanonicalMiddleFlags.{v} := by
  intro K _ _ _
  obtain ⟨c⟩ := hc K
  exact c.middleFlag h104 h20

/-- The literal Borel index completes the checked coset realization, giving
both quotient coordinate systems over every finite characteristic-two field. -/
theorem canonical_coordinates : MiddleFactors.CanonicalCoordinates.{v} :=
  canonical_coordinates_of_card SevenRestriction.Twenty.canonical_borel_coset_card

/-- The canonical coset module has a 105-dimensional invariant subspace
between constants and augmentation, with simple factors of dimensions 104
and 20 over the original characteristic-two coefficient field. -/
theorem canonical_middle_flags : CanonicalMiddleFlags.{v} :=
  canonical_middle_flags_of_coordinates_and_density canonical_coordinates
    MiddleFactors.binary_density_104 MiddleFactors.binary_density_20

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
