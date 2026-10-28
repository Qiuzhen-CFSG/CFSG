module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.TestFormData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.Contracts
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.InputChecks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.ContractionChecks

/-!
# Assembly of the packed quadratic coefficient certificate

The coefficient equality follows from four kernel-checked finite certificates
on the fixed arrays: source columns, form products, contractions, and
polarization. The assembly preserves each diagonal once and adds the reversed
coefficient only for strict upper pairs.

`equationRows_packed_coefficients` discharges all four numerical premises.
The separate actual-test-form calibration is neither imported nor assumed
here. Source: `../../source/README.md`.
-/

public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients
open PackedTable

/-- Soundness of the finite numerical certificates, with diagonal and strict
upper coefficients treated in their published conventions. -/
theorem equationRows_packed_coefficients_of_checks
    (hC : ∀ a : Fin 125, ColumnCheck a) (hD : ∀ t : Fin 10, ImageCheck t)
    (hc : ∀ e : Fin 987, ContractionCheck e) (hp : ∀ e : Fin 987, PolarizationCheck e)
    (e : Fin 987) (a b : Fin 125) (hab : a ≤ b) :
    bit (equationRows.get e) (slot a b) =
      bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
        (restrictionLinearRows.get a) (restrictionLinearRows.get b)) 0 +
      if a = b then 0 else
        bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
          (restrictionLinearRows.get b) (restrictionLinearRows.get a)) 0 := by
  have h := rowCheck_spec (equationRows.get e) (ordered.get e) (reversed.get e)
    a b hab (hp e a)
  have ho := ordered_coefficients_of_checks hC hD hc e a b
  rw [ho.1, ho.2] at h
  exact h

/-- The published quadratic rows have the packed pullback coefficients, with
each diagonal retained once and only off-diagonal coefficients polarized. -/
theorem equationRows_packed_coefficients (e : Fin 987) (a b : Fin 125) (hab : a ≤ b) :
    bit (equationRows.get e) (slot a b) =
      bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
        (restrictionLinearRows.get a) (restrictionLinearRows.get b)) 0 +
      if a = b then 0 else
        bit (pullbackBits (tests.get e).2 (testFormRows (tests.get e).1)
          (restrictionLinearRows.get b) (restrictionLinearRows.get a)) 0 :=
  equationRows_packed_coefficients_of_checks columns_checked images_checked
    contractions_checked polarizations_checked e a b hab

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients
