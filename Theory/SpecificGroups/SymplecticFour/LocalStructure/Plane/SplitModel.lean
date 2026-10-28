module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalCover
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A split model for the actual symplectic plane local

The existing block-diagonal Levi lifts form a homomorphic section of the
original quotient map. Multiplication of shears and Levi lifts, transported
through the full orthogonal-cover coordinates, gives an isomorphism with the
split orthogonal-cover group. Its equations retain the actual radical, the
original SL₂ quotient, and the chosen Levi section.

Source: Aschbacher--Smith, 2.4.8(4), and the plane-local calculation of
F.1.12(I)(2). The binary module is the maximal natural cover of I.2.3.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The multiplicative form of the full orthogonal-cover action. -/
@[expose] def multiplicativeAction : SL F →* MulAut (Multiplicative (Space F)) where
  toFun g := (LinearEquiv.ofBijective (action g) (action.apply_bijective g)).toAddEquiv.toMultiplicative
  map_one' := by ext v; exact congrArg Multiplicative.ofAdd (by simp)
  map_mul' g h := by ext v; exact congrArg Multiplicative.ofAdd (by simp)

@[simp] theorem multiplicativeAction_apply (g : SL F) (v : Multiplicative (Space F)) :
    (multiplicativeAction g v).toAdd = action g v.toAdd := rfl

/-- Restriction to binary scalars leaves the literal multiplicative action unchanged. -/
theorem multiplicativeAction_binary [Algebra (ZMod 2) F]
    (g : SL F) (v : Multiplicative (Space F)) :
    (multiplicativeAction g v).toAdd = binaryAction g v.toAdd := rfl

/-- The split group built from the maximal binary natural cover. -/
abbrev SplitGroup (F : Type*) [Field F] [Finite F] [CharP F 2] :=
  Multiplicative (Space F) ⋊[multiplicativeAction] SL F
end Representation.SL2OrthogonalCover

open Matrix
namespace Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover
open Representation.SL2OrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The existing Levi lifts form a homomorphic section. -/
@[expose] def leviHom : SL F →* planeLocal (F := F) where
  toFun := levi
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [levi_matrix, inv_one, SpecialLinearGroup.coe_one, transpose_one]
    exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change fromBlocks (g * h).val 0 0 ((g * h)⁻¹).valᵀ =
      fromBlocks g.val 0 0 (g⁻¹).valᵀ * fromBlocks h.val 0 0 (h⁻¹).valᵀ
    simp only [SpecialLinearGroup.coe_mul, _root_.mul_inv_rev,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add,
      add_zero, Matrix.transpose_mul]

omit [Finite F] [CharP F 2] in
@[simp] theorem leviHom_apply (g : SL F) : leviHom g = levi g := rfl

/-- The actual split extension map sends the radical and Levi factors to their original matrices. -/
@[expose] def splitHom : SplitGroup F →* planeLocal (F := F) :=
  SemidirectProduct.lift
    ((radical (F := F)).subtype.comp radicalCoordinates.symm.toMonoidHom)
    leviHom (fun g => by
      apply MonoidHom.ext
      intro v
      change (radicalCoordinates.symm (multiplicativeAction g v)).val =
        levi g * (radicalCoordinates.symm v).val * (levi g)⁻¹
      have h := radicalCoordinates_conjugate (levi g) (radicalCoordinates.symm v)
      rw [quotientMap_levi, MulEquiv.apply_symm_apply] at h
      have hh : radicalCoordinates (conjugate (levi g) (radicalCoordinates.symm v)) =
          multiplicativeAction g v := Multiplicative.toAdd.injective h
      rw [← hh, MulEquiv.symm_apply_apply]
      rfl)

@[simp] theorem splitHom_apply (x : SplitGroup F) :
    splitHom x = (radicalCoordinates.symm x.left).val * levi x.right := rfl

private def splitting (g : planeLocal (F := F)) : SplitGroup F :=
  ⟨radicalCoordinates ⟨g * (levi (quotientMap g))⁻¹, by
    change quotientMap (g * (levi (quotientMap g))⁻¹) = 1
    simp⟩, quotientMap g⟩

private theorem splitting_leftInverse : Function.LeftInverse (splitting (F := F)) splitHom := by
  intro x
  apply SemidirectProduct.ext
  · change radicalCoordinates ⟨splitHom x * (levi (quotientMap (splitHom x)))⁻¹, _⟩ = x.left
    apply radicalCoordinates.symm.injective
    simp only [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    change splitHom x * (levi (quotientMap (splitHom x)))⁻¹ = (radicalCoordinates.symm x.left).val
    rw [splitHom_apply, map_mul, (radicalCoordinates.symm x.left).property,
      quotientMap_levi, one_mul, mul_inv_cancel_right]
  · change quotientMap (splitHom x) = x.right
    rw [splitHom_apply, map_mul, (radicalCoordinates.symm x.left).property,
      quotientMap_levi, one_mul]

private theorem splitting_rightInverse : Function.RightInverse (splitting (F := F)) splitHom := by
  intro g
  change (radicalCoordinates.symm (radicalCoordinates ⟨g * (levi (quotientMap g))⁻¹, _⟩)).val *
    levi (quotientMap g) = g
  rw [MulEquiv.symm_apply_apply]
  exact inv_mul_cancel_right _ _

/-- The actual plane local is the split orthogonal-cover group over the same field. -/
def planeLocalEquiv : planeLocal (F := F) ≃* SplitGroup F :=
  (MulEquiv.ofBijective splitHom ⟨(splitting_leftInverse (F := F)).injective,
    (splitting_rightInverse (F := F)).surjective⟩).symm

@[simp] theorem planeLocalEquiv_symm_apply (x : SplitGroup F) :
    planeLocalEquiv.symm x = (radicalCoordinates.symm x.left).val * levi x.right := by rfl

/-- The marked SL₂ quotient remains the original upper-left block. -/
theorem planeLocalEquiv_quotient (g : planeLocal (F := F)) :
    (planeLocalEquiv g).right = quotientMap g := by
  obtain ⟨x, rfl⟩ := planeLocalEquiv.symm.surjective g
  rw [MulEquiv.apply_symm_apply, planeLocalEquiv_symm_apply, map_mul,
    (radicalCoordinates.symm x.left).property, quotientMap_levi, one_mul]

/-- The full original radical is sent to the left factor with the proved coordinates. -/
theorem planeLocalEquiv_radical (q : radical (F := F)) :
    planeLocalEquiv q.val = SemidirectProduct.inl (radicalCoordinates q) := by
  apply planeLocalEquiv.symm.injective
  rw [MulEquiv.symm_apply_apply, planeLocalEquiv_symm_apply]
  change q.val = (radicalCoordinates.symm (radicalCoordinates q)).val * levi 1
  rw [MulEquiv.symm_apply_apply, ← leviHom_apply, map_one, mul_one]

/-- The existing Levi section is sent to the right factor without changing SL₂. -/
theorem planeLocalEquiv_levi (g : SL F) :
    planeLocalEquiv (levi g) = SemidirectProduct.inr g := by
  apply planeLocalEquiv.symm.injective
  rw [MulEquiv.symm_apply_apply, planeLocalEquiv_symm_apply]
  change levi g = (radicalCoordinates.symm 1).val * levi g
  rw [map_one, Subgroup.coe_one, one_mul]

end Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover
