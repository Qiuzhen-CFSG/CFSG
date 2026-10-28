module

public import Theory.Representation.SpecialLinearThreeFrameGeometry.PlaneResidual.CoordinateCase

/-!
# Plane factorization and the prime-to-two residual for an SL₃ frame

Transport the coordinate affine-kernel calculation through a basis of the
three actual frame lines. The product factors are the generated point
radicals and the intersection of the two point stabilizers. The residual
is formed inside the plane stabilizer, then embedded into SL₃ by its subtype.
No lower bound on the field size is required.

Source: Aschbacher–Smith, G.2.5 proof, printed pp.335–336.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
open scoped MatrixGroups Pointwise


namespace Matrix.SpecialLinearGroup.FrameGeometry
open PlaneResidual
variable {F : Type*} [Field F] [Finite F]

/-- Set-product factorizations transport through a genuine group isomorphism. -/
theorem factorization_of_map {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (P Q R : Subgroup H)
    (he : (P.map e.toMonoidHom : Set K) =
      (Q.map e.toMonoidHom : Set K) * (R.map e.toMonoidHom : Set K)) :
    (P : Set H) = (Q : Set H) * (R : Set H) := by
  apply Set.image_injective.mpr e.injective
  rw [Set.image_mul e]
  exact he

/-- The plane stabilizer is the literal product of the two-radical group
and the common stabilizer of the two marked points. -/
theorem Frame.plane_factorization (b : Frame F) :
    (stabilizer (b.point 0 ⊔ b.point 1) : Set SL(3, F)) =
      (↑(pointRadical (b.point 0) ⊔ pointRadical (b.point 1)) : Set SL(3, F)) *
      (↑(stabilizer (b.point 0) ⊓ stabilizer (b.point 1)) : Set SL(3, F)) := by
  obtain ⟨c, hc⟩ := frame_basis b
  let e := coordinateChange c.equivFun
  have hP : (stabilizer (b.point 0 ⊔ b.point 1)).map e.toMonoidHom =
      PSL3.LinearThree.lineParabolicSL F := by
    rw [coordinateChange_stabilizer, Submodule.map_sup, hc 0, hc 1,
      basis_point_map, basis_point_map, coordinatePlane_stabilizer]
  have hQ : (pointRadical (b.point 0) ⊔ pointRadical (b.point 1)).map e.toMonoidHom =
      coordinatePair := by
    rw [Subgroup.map_sup, pointRadical, pointRadical, coordinateChange_root,
      coordinateChange_root, hc 0, hc 1, basis_point_map, basis_point_map]
    rfl
  have hR : (stabilizer (b.point 0) ⊓ stabilizer (b.point 1)).map e.toMonoidHom =
      stabilizer (coordinatePoint 0) ⊓ stabilizer (coordinatePoint 1) := by
    rw [Subgroup.map_inf _ _ _ e.injective, coordinateChange_stabilizer,
      coordinateChange_stabilizer, hc 0, hc 1, basis_point_map, basis_point_map]
  apply factorization_of_map e
  rw [hP, hQ, hR]
  exact coordinate_factorization

/-- The residual is taken inside the plane stabilizer and then embedded by
its subtype map. This holds over every finite characteristic-two field. -/
theorem Frame.plane_oddResidual [CharP F 2] (b : Frame F) :
    pointRadical (b.point 0) ⊔ pointRadical (b.point 1) =
      (piResidual {p : Nat.Primes | p.val ≠ 2} (stabilizer (b.point 0 ⊔ b.point 1))).map
        (stabilizer (b.point 0 ⊔ b.point 1)).subtype := by
  obtain ⟨c, hc⟩ := frame_basis b
  let e := coordinateChange c.equivFun
  have hP : (stabilizer (b.point 0 ⊔ b.point 1)).map e.toMonoidHom =
      PSL3.LinearThree.lineParabolicSL F := by
    rw [coordinateChange_stabilizer, Submodule.map_sup, hc 0, hc 1,
      basis_point_map, basis_point_map, coordinatePlane_stabilizer]
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_embedded_piResidual, hP, Subgroup.map_sup,
    pointRadical, pointRadical, coordinateChange_root, coordinateChange_root,
    hc 0, hc 1, basis_point_map, basis_point_map]
  exact coordinate_residual

end Matrix.SpecialLinearGroup.FrameGeometry

