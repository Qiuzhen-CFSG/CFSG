module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores

/-!
# Natural coordinates on the point radical

The affine marking identifies the actual point radical of SL₃ with the
additive plane. Conjugation is the natural action of the same affine
linear-part map. Both formulas retain the point-local inclusion; no
abstract identification of a group of order q² is used.

Source: Aschbacher--Smith F.1.12(I), pp.262--264, applied to the
cubic-fixed radical in the conclusion of original 4.3.2, pp.618--619.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

/-- Vector coordinates on the literal point radical. -/
noncomputable def pointRadicalCoordinates : pointRadicalSL F ≃* Multiplicative (Fin 2 → F) where
  toFun v := (pointLocalAffineEquiv F v).left
  invFun v := ⟨(pointLocalAffineEquiv F).symm (SemidirectProduct.inl v), by
    change (pointLocalAffineEquiv F ((pointLocalAffineEquiv F).symm _)).right = 1
    rw [MulEquiv.apply_symm_apply]
    rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply (pointLocalAffineEquiv F).injective
    rw [MulEquiv.apply_symm_apply]
    apply SemidirectProduct.ext
    · rfl
    · exact v.property.symm
  right_inv v := by simp
  map_mul' v w := by
    change (pointLocalAffineEquiv F ((v : pointLocalSL F) * w)).left = _
    rw [map_mul]
    change (pointLocalAffineEquiv F v).left *
      Matrix.SL2.naturalAction F (pointLocalAffineEquiv F v).right
        (pointLocalAffineEquiv F w).left = _
    have hv : (pointLocalAffineEquiv F v).right = 1 := v.property
    rw [hv,map_one]
    rfl

/-- The inclusion in the affine local is the translation by these coordinates. -/
theorem pointRadicalCoordinates_spec (v : pointRadicalSL F) :
    pointLocalAffineEquiv F v = SemidirectProduct.inl (pointRadicalCoordinates F v) := by
  apply SemidirectProduct.ext
  · rfl
  · exact v.property

/-- Conjugation preserves the original affine linear part. -/
theorem pointRadicalCoordinates_conjugate (k : pointLocalSL F)
    (v w : pointRadicalSL F) (hw : (w : pointLocalSL F) = k * v * k⁻¹) :
    pointRadicalCoordinates F w = Matrix.SL2.naturalAction F
      (pointLocalAffineEquiv F k).right (pointRadicalCoordinates F v) := by
  apply SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction F)
  rw [←pointRadicalCoordinates_spec,hw,map_mul,map_mul,map_inv,
    pointRadicalCoordinates_spec,Matrix.SL2.conjugate_inl]

end Matrix.PSL3.LinearThree
