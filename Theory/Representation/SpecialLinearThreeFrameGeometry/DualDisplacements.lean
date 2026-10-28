module

public import Theory.Representation.SpecialLinearThreeFrameGeometry

/-!
# Dual displacements of a point radical

Every functional vanishing on a nonzero subspace is a displacement of its
point radical. Choose a nonzero vector v in that subspace and a functional
e with e(v)=1. The inverse of the shear w ↦ w+f(w)v displaces e by f in
the contragredient action. This is an additive identity, so it also controls
restriction to the prime field.

The original solvable-residual calculation in Aschbacher--Smith, 11.5.7,
printed p.781, uses this identity on the dual layer.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.FrameGeometry
variable {F : Type*} [Field F]

/-- Every annihilating functional is a single dual displacement of the point radical. -/
theorem exists_pointRadical_dual_displacement
    (P : Submodule F (Fin 3 → F)) (hP : P ≠ ⊥)
    (f : Module.Dual F (Fin 3 → F)) (hf : f ∈ P.dualAnnihilator) :
    ∃ a ∈ pointRadical P, ∃ e : Module.Dual F (Fin 3 → F),
      natural.dual a e - e = f := by
  obtain ⟨v, hv, hv0⟩ := P.ne_bot_iff.mp hP
  obtain ⟨e, he⟩ := Module.Projective.exists_dual_eq_one F hv0
  have hfv := (Submodule.mem_dualAnnihilator f).mp hf v hv
  refine ⟨(shear f v hfv)⁻¹, (pointRadical P).inv_mem
    (shear_mem_root le_rfl v hv f hf), e, ?_⟩
  apply LinearMap.ext
  intro w
  change e (natural ((shear f v hfv)⁻¹⁻¹) w) - e w = f w
  rw [inv_inv, shear_apply, map_add, map_smul, he, smul_eq_mul, mul_one]
  abel

end Matrix.SpecialLinearGroup.FrameGeometry
