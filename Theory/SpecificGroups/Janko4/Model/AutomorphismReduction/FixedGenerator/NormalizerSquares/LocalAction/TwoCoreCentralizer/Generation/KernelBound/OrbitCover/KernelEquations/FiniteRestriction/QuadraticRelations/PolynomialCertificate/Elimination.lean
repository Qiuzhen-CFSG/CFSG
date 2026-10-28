module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target0
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target2
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target3
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target4
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target5
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target6
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target7
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Elimination.Target8

/-!
# Boolean elimination of the finite restriction equations

The 987 equation rows and normalization force the nine target quadrics to
vanish over GF(2). First multiply normalization by each variable. Kernel-checked
Gaussian combinations of these 1113 inputs give 78 affine relations. Each target
is then certified as a sum of input equations and affine multiples of those
relations, in the original upper triangular monomial order. The algebra layer
proves the Boolean reductions, including every diagonal square.

The certificates derive from `source/witnesses.json`; the conversion to ideal
identities is reproducible with `Elimination/source/generate_bounded.py`. Matrix semantics
and the deduction of the normalization premise belong to the parent assembly.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate

/-- The normalized polynomial equations imply all nine target quadrics. -/
theorem targetRows_zero_of_equations (x : Coefficients)
    (heq : ∀ e : Fin 987, eval (equationRows.get e) x = 0)
    (hnorm : eval normalizationRow x = 0) :
    ∀ i : Fin 9, eval (targetRows.get i) x = 0 := by
  have hinputs := Elimination.inputRows_zero x heq hnorm
  have hvalues := Elimination.valueAffines_zero x hinputs
  intro i
  fin_cases i
  · exact Elimination.target0_zero x hinputs hvalues
  · exact Elimination.target1_zero x hinputs hvalues
  · exact Elimination.target2_zero x hinputs hvalues
  · exact Elimination.target3_zero x hinputs hvalues
  · exact Elimination.target4_zero x hinputs hvalues
  · exact Elimination.target5_zero x hinputs hvalues
  · exact Elimination.target6_zero x hinputs hvalues
  · exact Elimination.target7_zero x hinputs hvalues
  · exact Elimination.target8_zero x hinputs hvalues

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
