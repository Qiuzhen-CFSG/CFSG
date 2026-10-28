module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1
public import Mathlib.GroupTheory.OrderOfElement

/-!
# An involution in the fixed binary Co₁ carrier

The first ATLAS generator squares to one by the checked matrix certificate.
Its (0,1)-entry distinguishes it from the identity. This proves that the fixed
carrier contains an involution; it does not identify its centralizer or assert
an ATLAS conjugacy-class label.

Source: the `Co1G1-f2r24B0` matrices and provenance in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/`.
-/

@[expose] public section

namespace Sporadic.LeechRelated.Co1

/-- The first ATLAS generator, regarded as an element of the generated group. -/
def involution : Carrier :=
  ⟨generatorA, Subgroup.subset_closure (by simp)⟩

theorem involution_sq : involution ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change matrixA ^ 2 = 1
  simpa only [pow_two] using matrixA_square

theorem involution_ne_one : involution ≠ 1 := by
  intro h
  have hentry := congrArg (fun x : Carrier => (x.val.val :
    Matrix (Fin 24) (Fin 24) (ZMod 2)) 0 1) h
  change (1 : ZMod 2) = 0 at hentry
  exact one_ne_zero hentry

theorem involution_order : orderOf involution = 2 :=
  orderOf_eq_prime involution_sq involution_ne_one

end Sporadic.LeechRelated.Co1
