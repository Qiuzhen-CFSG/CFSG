module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.Chart
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients

/-!
# Matrix semantics of the polynomial restriction table

The normalization and nine target rows have their unconditional chart
interpretations, re-exported from Chart. The selected equations are evaluations
of upper triangular functionals on matrix pullbacks. PullbackCoefficients
certifies their constant and diagonal/polarized coefficients, and
ExteriorAnnihilators certifies vanishing of the selected functionals on all
1221 original exterior generators. The final assembly discharges every finite
certificate premise: pairing preservation and membership in the actual exterior
span imply vanishing of all 987 selected equations.

Source and ATLAS conventions: PolynomialCertificate/source/README.md and
OrbitCover/Coordinates. No group membership or normalization is used here.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates

/-- A coefficient certificate identifies a selected row with its matrix test. -/
theorem equationRows_eval_of_coefficients (e : Fin 987)
    (hconst : bit (equationRows.get e) 0 =
      if (tests.get e).1.val = 0 then upperValue (tests.get e).2 restrictionPairing else 0)
    (hcoeff : ∀ a b : Fin 125, a ≤ b →
      bit (equationRows.get e) (slot a b) =
        pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) a b +
          if a = b then 0 else
            pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) b a)
    (x : Coefficients) :
    eval (equationRows.get e) x = constraintValue (tests.get e) (coefficientMatrix x) := by
  rw [eval_pullback_of_coefficients _ _ _ _ hconst hcoeff]
  exact add_comm _ _

/-- Conditional assembly of the two finite certificates against the actual
pairing and exterior membership hypotheses. -/
theorem equationRows_zero_of_certificates (x : Coefficients)
    (hpair : (coefficientMatrix x)ᵀ * restrictionPairing * coefficientMatrix x =
      restrictionPairing)
    (hext : ∀ i : Fin 9,
      (coefficientMatrix x)ᵀ * restrictionTestForm i * coefficientMatrix x ∈
        restrictionExteriorSpace)
    (hconst : ∀ e : Fin 987, bit (equationRows.get e) 0 =
      if (tests.get e).1.val = 0 then upperValue (tests.get e).2 restrictionPairing else 0)
    (hcoeff : ∀ e : Fin 987, ∀ a b : Fin 125, a ≤ b →
      bit (equationRows.get e) (slot a b) =
        pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) a b +
          if a = b then 0 else
            pullbackCoefficient (tests.get e).2 (testForm (tests.get e).1) b a)
    (hann : ∀ e : Fin 987, (tests.get e).1.val ≠ 0 → ∀ a : Fin 1221,
      upperValue (tests.get e).2 (restrictionForm (exteriorBasisForm a)) = 0) :
    ∀ e : Fin 987, eval (equationRows.get e) x = 0 := by
  intro e
  rw [equationRows_eval_of_coefficients e (hconst e) (hcoeff e)]
  exact constraintValue_zero (tests.get e) (coefficientMatrix x) hpair hext (hann e)

/-- Pairing preservation and membership of the nine pulled-back test forms in
the actual exterior span force every selected polynomial equation to vanish. -/
theorem equationRows_zero_of_matrix (x : Coefficients)
    (hpair : (coefficientMatrix x)ᵀ * restrictionPairing * coefficientMatrix x =
      restrictionPairing)
    (hext : ∀ i : Fin 9,
      (coefficientMatrix x)ᵀ * restrictionTestForm i * coefficientMatrix x ∈
        restrictionExteriorSpace) :
    ∀ e : Fin 987, eval (equationRows.get e) x = 0 :=
  equationRows_zero_of_certificates x hpair hext equationRows_constant
    equationRows_coefficients tests_annihilate_exterior

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
