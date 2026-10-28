module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.MiddleResidual
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# Full movement by the exterior point residual

The solvable residual of the two-space parabolic moves the entire exterior
square. For each wedge basis vector, a transvection in its identity-small-block
kernel realizes that vector as an action difference. These ten identities prove
[V, N_L(V₁)∞] = V after transport through the original exterior marking.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820, using 12.5.2(1).
-/

public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Subgroup

private theorem elementary_mem_pointResidual (i j : Fin 5) (hij : i ≠ j)
    (hj : 2 ≤ j.val) : elementary i j ∈ parabolicResidual 2 := by
  rw [parabolicResidual_two]
  have hp : elementary i j ∈ parabolic 2 := by
    rw [parabolic_eq_closure_transvections]
    exact subset_closure ⟨i, j, hij, 1, (by omega), by simp [elementary, hij]⟩
  refine ⟨⟨_, hp⟩, ?_, rfl⟩
  change parabolicTwoSmallBlock ⟨_, hp⟩ = 1
  apply Subtype.ext
  ext a b
  rw [parabolicTwoSmallBlock_entry]
  have hjb : j.val ≠ b.val := by have := b.isLt; omega
  simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single, Matrix.one_apply, Fin.ext_iff, hjb]

private def targetIndex : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
private def sourceIndex : Fin 10 → Fin 5 := ![2,3,2,2,3,2,2,4,3,2]
private def inputIndex : Fin 10 → Fin 10 := ![4,7,7,8,7,7,8,9,9,8]

private theorem point_difference (t : Fin 10) :
    exteriorAction 2 (elementary (targetIndex t) (sourceIndex t)) (basis (inputIndex t)) -
      basis (inputIndex t) = basis t := by
  apply coordinates.injective
  rw [map_sub, coordinates_action, coordinates_basis, coordinates_basis]
  fin_cases t <;> decide +kernel

theorem pointResidual_commutator_eq_top :
    BinaryOffender.subspaceCommutator (exteriorAction 2) ⊤ (parabolicResidual 2) = ⊤ := by
  apply top_unique
  rw [← basis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  rw [← point_difference t]
  apply Submodule.subset_span
  exact ⟨elementary (targetIndex t) (sourceIndex t),
    elementary_mem_pointResidual _ _
      ((by decide : ∀ t, targetIndex t ≠ sourceIndex t) t)
      ((by decide : ∀ t, 2 ≤ (sourceIndex t).val) t),
    basis (inputIndex t), Submodule.subset_span ⟨inputIndex t, rfl⟩, rfl⟩

end Representation.SL5ExteriorSquare
