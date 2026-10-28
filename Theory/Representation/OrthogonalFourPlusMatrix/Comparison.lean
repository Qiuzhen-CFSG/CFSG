module

public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.Image
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary

/-!
# The determinant model and the actual split orthogonal group in dimension four

The left-right action has exactly the Siegel-generated elementary image.
In characteristic two it is faithful, and the elementary scalar quotient has
trivial kernel. Their composition therefore identifies the two SL₂ factors
with the existing `POmegaPlus 2 F`, equivariantly on the natural module.
The final identity specializes these same coordinates to the binary F₄ module.

Source application: Aschbacher–Smith 13.8.16(1), printed pp.952–953.
The generator comparison is adapted from ATLAS in the imported descendants.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]

/-- The determinant action has precisely the existing elementary orthogonal image. -/
theorem range_eq_elementary :
    (toOrthogonal (F := F)).range = elementarySubgroup (formD 2 F) :=
  le_antisymm image_le_elementary elementary_le_image

/-- The determinant action, with codomain restricted to its actual elementary image. -/
def toElementary : PairSL (F := F) →* elementarySubgroup (formD 2 F) :=
  toOrthogonal.codRestrict _ toOrthogonal_mem_elementary

@[simp] theorem toElementary_val (g : PairSL (F := F)) :
    (toElementary g).val = toOrthogonal g := rfl

/-- Every elementary isometry is realized by a pair of special linear matrices. -/
theorem toElementary_surjective : Function.Surjective (toElementary (F := F)) := by
  intro g
  obtain ⟨a, ha⟩ := elementary_le_image g.prop
  exact ⟨a, Subtype.ext ha⟩

variable [CharP F 2]

/-- The quadratic-space action inherits the faithfulness of the matrix action. -/
theorem toOrthogonal_injective : Function.Injective (toOrthogonal (F := F)) := by
  intro a b hab
  apply matrixHom_injective
  apply LinearEquiv.ext
  intro M
  change a.1.val * M * a.2⁻¹.val = b.1.val * M * b.2⁻¹.val
  have h := congrArg (fun g : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formD 2 F) =>
    coordinates (g.val (coordinates.symm M))) hab
  simpa only [toOrthogonal_coordinates, LinearEquiv.apply_symm_apply] using h

/-- The two special linear factors are the actual elementary orthogonal carrier. -/
def elementaryEquiv : PairSL (F := F) ≃* elementarySubgroup (formD 2 F) :=
  MulEquiv.ofBijective toElementary
    ⟨fun _ _ h => toOrthogonal_injective (congrArg Subtype.val h), toElementary_surjective⟩

@[simp] theorem elementaryEquiv_apply (g : PairSL (F := F)) :
    elementaryEquiv g = toElementary g := rfl

/-- The actual multiplicative equivalence to the existing projective Omega carrier. -/
def projectiveEquiv : PairSL (F := F) ≃* POmegaPlus 2 F :=
  elementaryEquiv.trans (elementaryProjectiveEquiv (formD 2 F))

@[simp] theorem projectiveEquiv_apply (g : PairSL (F := F)) :
    projectiveEquiv g = projectiveElementaryMap (formD 2 F) (toElementary g) := rfl

/-- Determinant coordinates intertwine the actual projective natural representation. -/
theorem projectiveEquiv_coordinates (g : PairSL (F := F)) (v : VectorD 2 F) :
    coordinates (projectiveElementaryNatural (formD 2 F) (projectiveEquiv g) v) =
      representation g (coordinates v) := by
  rw [projectiveEquiv_apply, projectiveElementaryNatural_mk]
  exact toOrthogonal_coordinates g v

namespace Binary

/-- The concrete `SL₂(4) × SL₂(4)` determinant model is the existing `PΩ₄⁺(4)`. -/
def orthogonalEquiv : G ≃* POmegaPlus 2 Binary.F := projectiveEquiv

/-- The same comparison intertwines determinant coordinates after restriction to F₂. -/
theorem binaryCoordinates_projective_equivariant (g : G) (v : VectorD 2 Binary.F) :
    binaryCoordinates
      (projectiveElementaryNatural (formD 2 Binary.F) (orthogonalEquiv g) v) =
      action g (binaryCoordinates v) :=
  projectiveEquiv_coordinates g v

end Binary
end ClassicalOrthogonal.FourPlusMatrix
