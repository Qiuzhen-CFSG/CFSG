module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Projective inverse-transpose coordinates

These interfaces retain the natural matrix coordinates of a projective graph
involution. They specify equations in the actual PGL image, so scalar changes
of special-unitary representatives are permitted. The adjoint transport in
`AdjointTransport` removes exactly those scalar factors.

The existence of these coordinates for an arbitrary outer involution is a
separate group-theoretic obligation; these definitions do not assert it.
Source: GM04, Proposition 4.11, internal pp.31--32, and GLS III, 2.5.12, 2.7,
and 4.9.2.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
variable {K : Type*} [Field K]

/-- The literal inverse-transpose automorphism on the natural matrix group. -/
@[expose] def inverseTranspose : GL (Fin 3) K →* GL (Fin 3) K where
  toFun A :=
    { val := (A⁻¹).val.transpose
      inv := A.val.transpose
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := by apply Units.ext; exact Matrix.transpose_one
  map_mul' A B := by
    apply Units.ext
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

@[simp] theorem inverseTranspose_val (A : GL (Fin 3) K) :
    (inverseTranspose A).val = (A⁻¹).val.transpose := rfl

variable {F H : Type*} [Field F] [Group H]

/-- Coordinates on natural matrices implementing the specified projective
SU₃ automorphism. This is an explicit matrix obligation, not its existence theorem. -/
@[expose] def HasProjectiveTransposeCoordinates (J : HermitianForm 3 F)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ C : GL (Fin 3) F, ∀ g : J.specialSubgroup,
    (ProjGenLinGroup.mk C)⁻¹ * (a (J.specialToProjective g)).val * ProjGenLinGroup.mk C =
      ProjGenLinGroup.mk (inverseTranspose (C⁻¹ * g.val * C))

/-- The representative-wise version for a specified quotient of SU₃. -/
@[expose] def HasMatrixTransposeCoordinates (J : HermitianForm 3 F)
    (p : J.specialSubgroup →* H) (α : MulAut H) : Prop :=
  ∃ C : GL (Fin 3) F, ∀ g h : J.specialSubgroup, p h = α (p g) →
    ProjGenLinGroup.mk (C⁻¹ * h.val * C) =
      ProjGenLinGroup.mk (inverseTranspose (C⁻¹ * g.val * C))

/-- Compatible quotient actions transport projective coordinates to all actual
special-unitary representatives, without choosing a faithful lift. -/
theorem matrixCoordinates_of_projectiveCoordinates (J : HermitianForm 3 F)
    (p : J.specialSubgroup →* H) (α : MulAut H)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : HasProjectiveTransposeCoordinates J a)
    (hp : ∀ g h, p h = α (p g) →
      J.specialToProjective h = a (J.specialToProjective g)) :
    HasMatrixTransposeCoordinates J p α := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨C, fun g h hgh => ?_⟩
  calc
    ProjGenLinGroup.mk (C⁻¹ * h.val * C) =
        (ProjGenLinGroup.mk C)⁻¹ * (J.specialToProjective h).val * ProjGenLinGroup.mk C := by
      rw [J.specialToProjective_apply_val]
      simp only [map_mul, map_inv]
    _ = _ := by rw [hp g h hgh]; exact hC g

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
