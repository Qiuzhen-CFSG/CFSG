module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Constants
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.TestFormData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.TestFormCalibration

/-!
# Relating selected polynomial coefficients to matrix pullbacks

The constant terms are certified unconditionally in `PullbackCoefficients.Constants`.
Packed matrix multiplication and transpose have their ordinary matrix semantics
in `PullbackCoefficients.Arithmetic`.

For the quadratic coefficients, `TestFormCalibration` identifies the packed
test-form rows with the actual restricted matrices, and `PackedTable` certifies
their polarized coefficients. The assembly below combines both certificates
with the arithmetic semantics. Each diagonal coefficient is retained once;
the reversed coefficient is added only off the diagonal. Both exported
coefficient identities are unconditional.

Source: the polynomial certificate's `source/README.md`; the actual restriction
matrices and ATLAS convention are in `QuadraticRelations.RestrictionData`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates PullbackCoefficients

/-- A finite identity in packed rows gives the desired matrix coefficient
once the candidate test-form rows have been calibrated. -/
theorem equationRows_coefficients_of_packed
    (hforms : ∀ t : Fin 10, decodeRestrictionRows (testFormRows t) = testForm t)
    (hcoeff : ∀ e : Fin 987, ∀ a b : Fin 125, a ≤ b →
      bit (equationRows.get e) (slot a b) =
        bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
          (restrictionLinearRows.get a) (restrictionLinearRows.get b)) 0 +
        if a = b then 0 else
          bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
            (restrictionLinearRows.get b) (restrictionLinearRows.get a)) 0)
    (e : Fin 987) (a b : Fin 125) (hab : a ≤ b) :
    bit (equationRows.get e) (slot a b) =
      pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) a b +
        if a = b then 0 else
          pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) b a := by
  rw [hcoeff e a b hab]
  simp only [pullbackBits_spec, hforms, pullbackCoefficient, restrictionLinearBasis]

/-- The selected rows have the quadratic coefficients of the actual matrix
pullbacks, retaining each diagonal once and polarizing only off the diagonal. -/
theorem equationRows_coefficients (e : Fin 987) (a b : Fin 125) (hab : a ≤ b) :
    bit (equationRows.get e) (slot a b) =
      pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) a b +
        if a = b then 0 else
          pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) b a :=
  equationRows_coefficients_of_packed testFormRows_spec equationRows_packed_coefficients
    e a b hab

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
