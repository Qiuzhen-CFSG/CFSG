module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerThirdModel

/-!
# Coordinates on the full fixed third overlap

The projective A₅ lies in the derived subgroup and therefore acts trivially
on the actual cubic kernel. The full preimage is thus a direct product,
with the first coordinate equal to its literal semidirect-product kernel
coordinate. No cubic kernel is lost in passing to the projective factor.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup

private theorem five_derived : thirdFive ≤ derived := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect thirdFive := Group.IsPerfect.ofSurjective
    (f := thirdFive_equiv.some.symm.toMonoidHom) thirdFive_equiv.some.symm.surjective
  rw [←thirdFive.commutator_eq_self]
  exact commutator_mono le_top le_top

@[expose] def splitCoordinates : thirdOverlap ≃* Z × thirdFive where
  toFun x := (x.val.left,⟨x.val.right,x.property⟩)
  invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Prod.ext
    · change x.val.left * action x.val.right y.val.left = x.val.left * y.val.left
      have hx : x.val.right ∈ action.ker := action_ker.symm ▸ five_derived x.property
      have hact : action x.val.right = 1 := hx
      rw [hact, MulAut.one_apply]
    · rfl

/-- Full direct-product coordinates on the canonical order-180 overlap. -/
@[expose] def thirdCoordinates : thirdOverlap ≃* Z × alternatingGroup (Fin 5) :=
  (show thirdOverlap ≃* Z × thirdFive from splitCoordinates).trans (MulEquiv.prodCongr (MulEquiv.refl Z) thirdFive_equiv.some)

/-- The cubic coordinate is exactly the original kernel coordinate. -/
theorem thirdCoordinates_fst (x : thirdOverlap) : (thirdCoordinates x).1 = x.val.left := by
  change (splitCoordinates x).1 = x.val.left
  rfl
end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
