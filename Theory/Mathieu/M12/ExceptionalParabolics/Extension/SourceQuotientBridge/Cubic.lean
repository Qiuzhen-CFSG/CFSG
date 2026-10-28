module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SourceQuotientBridge

/-!
# An actual first-parabolic cubic in the marked wreath coordinates

The square of the already word-certified cubic actor acts on both original
quaternion factors by q8Cycle and fixes the actual nonsplit swap. Hence its
conjugation on the whole core induces precisely FourWreathTwo.cubic through
the existing quotient map. No replacement of the core or its markings occurs.

Source: Aschbacher--Smith 14.2.21, printed p.988, refs/quasithin.pdf.
-/

@[expose] public section

open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
namespace Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge
open GLS3.Chapter5.SchurPresentation (q8Cycle)
open QuaternionSwapModel.WreathCoordinates (wreathEquiv)
set_option maxRecDepth 10000
attribute [local irreducible] z nonsplitSwap leftI leftJ rightI rightJ

def alignedCubic (m : InnerModel) : firstParabolic :=
  ⟨cubicActor ^ 2, firstParabolic.pow_mem (by
    obtain ⟨x,_,hx⟩ := cubicActor_mem_residual_image m
    exact hx ▸ x.property) 2⟩

private def alignedPerm : Equiv.Perm (Fin 24) where
  toFun := ![21,1,13,3,4,20,6,2,9,19,15,5,12,7,14,17,0,10,22,8,11,16,23,18]
  invFun := ![16,1,7,3,4,11,6,13,19,8,17,20,12,2,14,10,21,15,23,9,5,0,18,22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem alignedCubic_val (m : InnerModel) : (alignedCubic m).val.val = alignedPerm := by
  change (cubicActor ^ 2).val = alignedPerm
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

theorem alignedCubic_coordinate (m : InnerModel) (q r : QuaternionGroup 2) (b : Bool) :
    outerConjugation (firstParabolic_normalizes_outerCore m) (alignedCubic m)
      (coordinate q r b) = coordinate (q8Cycle q) (q8Cycle r) b := by
  apply Subtype.ext
  apply Subtype.ext
  change (alignedCubic m).val.val * (coordinate q r b).val.val *
    (alignedCubic m).val.val⁻¹ = (coordinate (q8Cycle q) (q8Cycle r) b).val.val
  rw [alignedCubic_val, coordinate_val, coordinate_val]
  have hc : ∀ q r : QuaternionGroup 2, ∀ b : Bool,
      alignedPerm * coordinatePerm q r b * alignedPerm⁻¹ =
        coordinatePerm (q8Cycle q) (q8Cycle r) b := by decide +kernel
  exact hc q r b

theorem alignedCubic_conjugation (m : InnerModel) (x : outerCore) :
    wreathMap m (outerConjugation (firstParabolic_normalizes_outerCore m)
      (alignedCubic m) x) = FourWreathTwo.cubic (wreathMap m x) := by
  obtain ⟨q,r,b,rfl⟩ := coordinate_surjective m x
  rw [alignedCubic_coordinate]
  change wreathEquiv (outerWreathMap m (coordinate (q8Cycle q) (q8Cycle r) b)) =
    FourWreathTwo.cubic (wreathEquiv (outerWreathMap m (coordinate q r b)))
  rw [outerWreathMap_coordinate, outerWreathMap_coordinate]
  have he : ∀ q r : QuaternionGroup 2, ∀ b : Bool,
      wreathEquiv (wreathCoordinate (q8Cycle q) (q8Cycle r) b) =
        FourWreathTwo.cubic (wreathEquiv (wreathCoordinate q r b)) := by decide +kernel
  exact he q r b

theorem action_alignedCubic (m : InnerModel) : action m (alignedCubic m) = FourWreathTwo.cubic := by
  apply MulEquiv.ext
  intro w
  obtain ⟨x,rfl⟩ := wreathMap_surjective m w
  rw [action_evaluation, alignedCubic_conjugation]

end Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge
