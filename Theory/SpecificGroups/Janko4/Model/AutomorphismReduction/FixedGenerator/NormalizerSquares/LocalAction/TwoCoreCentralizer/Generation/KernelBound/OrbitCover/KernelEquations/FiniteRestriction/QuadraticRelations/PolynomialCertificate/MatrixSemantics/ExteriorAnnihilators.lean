module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks000
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks016
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks032
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks048
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks064
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks080
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks096
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks112
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks128
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks144
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks160
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks176
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks192
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks208
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Checks224
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.Basis

/-!
# Annihilation of every actual exterior generator

Each nonzero-block functional from the polynomial table is transported through
the actual restriction embedding. Its binary matrix pairing vanishes on all
1221 full forms, already identified with the published decoded exterior rows.
No group, chart, membership, or elimination hypothesis is used.

ATLAS provenance and the certificate convention: ExteriorAnnihilators/source/README.md.
-/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators
open PullbackCoefficients ExteriorInvariance

theorem weights_annihilate (k : Fin 237) (a : Fin 1221) :
    upperValue (weights.get k) (restrictionForm (exteriorBasisForm a)) = 0 := by
  have hc : (∀ i : Fin 112, transportRow (weights.get k) i = flatRow (duals.get k) i.val) ∧
      (∀ b : Fin 1221, flatDot (duals.get k) (basisFlat b.val) = false) := by
    have hk := k.isLt
    by_cases h16 : k.val < 16
    · exact checks000 k.val (by omega) h16 hk
    by_cases h32 : k.val < 32
    · exact checks016 k.val (by omega) h32 hk
    by_cases h48 : k.val < 48
    · exact checks032 k.val (by omega) h48 hk
    by_cases h64 : k.val < 64
    · exact checks048 k.val (by omega) h64 hk
    by_cases h80 : k.val < 80
    · exact checks064 k.val (by omega) h80 hk
    by_cases h96 : k.val < 96
    · exact checks080 k.val (by omega) h96 hk
    by_cases h112 : k.val < 112
    · exact checks096 k.val (by omega) h112 hk
    by_cases h128 : k.val < 128
    · exact checks112 k.val (by omega) h128 hk
    by_cases h144 : k.val < 144
    · exact checks128 k.val (by omega) h144 hk
    by_cases h160 : k.val < 160
    · exact checks144 k.val (by omega) h160 hk
    by_cases h176 : k.val < 176
    · exact checks160 k.val (by omega) h176 hk
    by_cases h192 : k.val < 192
    · exact checks176 k.val (by omega) h192 hk
    by_cases h208 : k.val < 208
    · exact checks192 k.val (by omega) h208 hk
    by_cases h224 : k.val < 224
    · exact checks208 k.val (by omega) h224 hk
    exact checks224 k.val (by omega) hk hk
  rw [← basis_decode a]
  exact upperValue_zero_of_flat _ _ _ hc.1 (hc.2 a)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate

/-- Every selected exterior functional annihilates every original restricted generator. -/
theorem tests_annihilate_exterior : ∀ e : Fin 987, (tests.get e).1.val ≠ 0 →
    ∀ a : Fin 1221, upperValue (tests.get e).2 (restrictionForm (exteriorBasisForm a)) = 0 := by
  intro e he a
  rw [ExteriorAnnihilators.testIndex_spec e he]
  exact ExteriorAnnihilators.weights_annihilate _ a

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
