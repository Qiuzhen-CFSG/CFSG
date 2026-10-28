module

public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicNormal

/-!
# Coverage adapter for the PSL₃ cyclic-normal outer condition

Explicit standard-automorphism coverage upgrades the relative diagonal
normality and abelian field–graph quotient to the ambient outer group.
The existing cyclic-diagonal calculation then supplies a cyclic normal
subgroup whose quotient has cyclic odd-prime subgroups. Coverage is the
only extra input; the structural premises are discharged here.

Source: GLS3, Theorem 2.5.12(b–e,i), §2.7; Aschbacher–Smith,
combined 1 March 2004 manuscript, printed p.510.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.OuterSolvable

/-- The cyclic-normal condition on the actual outer group follows from
standard coverage, with normality and quotient commutativity proved. -/
theorem outer_cyclicNormalOddQuotient_of_standard_coverage
    (F : Type*) [Field F] [Finite F] (hcover : standard F = ⊤) :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer PSL(3,F)) := by
  let := innerDiagonalOuter_normal_of_coverage F hcover
  let := outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  exact outer_cyclicNormalOddQuotient_of_standard_inputs F hcover

end Matrix.PSL3.OuterSolvable
