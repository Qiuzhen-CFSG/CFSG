module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.RestrictionData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination

/-!
# Finite polynomial certificate for the restriction matrices

Pairing preservation and the nine exterior conditions force the nine chart
quadrics for a normalized matrix in the displayed restriction space. The proof
synthesizes its 125 coefficients from span membership, interprets the matrix
conditions through `MatrixSemantics`, and applies the Boolean certificate in
`Elimination`. Coordinate-zero normalization explicitly removes the
homogenizing factor in each target.

See `PolynomialCertificate/source/README.md` for the exact contract, retained
source data, complete Gaussian witnesses, and conventions. No ancestor assembly
or the independent ambient linear-membership proof is imported here.
-/

public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate

/-- The normalized pairing and exterior constraints imply all nine chart
quadrics on the displayed restriction space. -/
theorem quadratic_relations_of_restriction
    (S : RestrictionMatrix) (hS : S ∈ restrictionLinearSpace)
    (hpair : Sᵀ * restrictionPairing * S = restrictionPairing)
    (hext : ∀ i : Fin 9, Sᵀ * restrictionTestForm i * S ∈ restrictionExteriorSpace)
    (hzero : coordinates (restrictionImage S) 0 = 1) :
    ∀ i : Fin 9, coordinates (restrictionImage S) (quadraticIndex i) =
      quadraticCoordinate i (freeCoordinates (restrictionImage S)) := by
  obtain ⟨x, rfl⟩ := exists_coefficients_of_mem hS
  have hnorm : eval normalizationRow x = 0 := by
    rw [normalizationRow_eval, hzero]
    decide
  have htargets := targetRows_zero_of_equations x
    (equationRows_zero_of_matrix x hpair hext) hnorm
  intro i
  have hi := htargets i
  rw [targetRows_eval] at hi
  exact quadratic_eq_of_normalized_target _ i hzero hi

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
