module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicImage
public import Mathlib.RingTheory.IntegralDomain

/-!
# The cyclic diagonal outer image of PSL₃

The determinant kernel acts by inner automorphisms. Thus the actual GL₃
image in Aut/Inn is an image of a subgroup of the finite field's cyclic
unit group. This proves cyclicity, without full automorphism coverage or
a splitting. Source: GLS3, Theorem 2.5.12(c), and §2.7.
-/

public section
namespace Matrix.PSL3.OuterSolvable
open scoped MatrixGroups

/-- The diagonal image in the actual outer group is cyclic over a finite field. -/
theorem innerDiagonalOuter_isCyclic (F : Type*) [Field F] [Finite F] :
    IsCyclic (innerDiagonalOuter F) :=
  Theory.GroupTheory.isCyclic_range_of_ker_le_cyclic GeneralLinearGroup.det
    (linearOuterAction F) (det_ker_le_linearOuterAction_ker F)

end Matrix.PSL3.OuterSolvable
