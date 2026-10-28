module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Five

/-! The full original third overlap is C₃ × A₅ with its cubic coordinate retained. -/
public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup OverlapTables SourceRecognition.CubicNormalizerModel

private def projectivePreimageSplit : Third.subgroup.comap projection ≃* Z × Third.subgroup where
  toFun x := (x.val.left,⟨x.val.right,x.property⟩)
  invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Prod.ext
    · change x.val.left * SourceRecognition.CubicNormalizerModel.action x.val.right y.val.left =
        x.val.left * y.val.left
      have hx : x.val.right ∈ SourceRecognition.CubicNormalizerModel.action.ker :=
        action_ker.symm ▸ rawThirdProjection_le_derived x.property
      have hact : SourceRecognition.CubicNormalizerModel.action x.val.right = 1 := hx
      rw [hact,MulAut.one_apply]
    · rfl

/-- The actual raw order-180 subgroup has direct-product coordinates C₃ × A₅. -/
def rawThirdEquiv : rawThird ≃* Z × alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr rawThird_eq_comap).trans
    (projectivePreimageSplit.trans (MulEquiv.prodCongr (MulEquiv.refl Z) rawThirdProjectionEquiv))

/-- Direct-product recognition preserves the entire original cubic coordinate. -/
theorem rawThirdEquiv_fst (x : rawThird) : (rawThirdEquiv x).1 = x.val.left := by
  simp only [rawThirdEquiv,MulEquiv.trans_apply]
  rfl

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
