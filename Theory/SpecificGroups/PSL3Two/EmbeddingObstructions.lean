module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels

/-!
# Two local obstructions to embedding PSL₃(2)

A Sylow two-subgroup is dihedral of order eight, so it contains noncommuting
involutions. A Singer cycle is conjugate to its square by the binary Frobenius
matrix. These exclude embeddings in groups with commuting Sylow involutions
and in symplectic four-space in characteristic two, respectively.

The dihedral model is the explicit binary unitriangular construction in the
imported module. The Singer matrices express multiplication and squaring in
F₂[X]/(X³+X+1). These calculations are used in the model inspection in
Aschbacher--Smith, proof of 15.3.38, printed p.1137.
-/

public section
namespace Matrix.PSL3Two
open Subgroup

/-- Commuting involutions in one Sylow two-subgroup obstruct a faithful
PSL₃(2) embedding. -/
theorem not_injective_of_sylow_involutions_commute {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G)
    (hP : ∀ a b : P, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b)
    (f : PSL →* G) : ¬ Function.Injective f := by
  intro hf
  let R : Sylow 2 PSL := default
  obtain ⟨e⟩ := PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral R
  obtain ⟨Q, hQ⟩ := (R.isPGroup'.map f).exists_le_sylow
  let q : Q ≃* P := Q.equiv P
  let r : R →* P := q.toMonoidHom.comp
    ((f.comp (R : Subgroup PSL).subtype).codRestrict Q
      (by intro z; exact hQ ⟨z, z.property, rfl⟩))
  have hr : Function.Injective r := by
    intro z w h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val (q.injective h)
  let j := r.comp e.symm.toMonoidHom
  have hj : Function.Injective j := hr.comp e.symm.injective
  have hs (i : ZMod 4) : j (.sr i) ^ 2 = 1 := by
    rw [← map_pow]
    have h : (DihedralGroup.sr i) ^ 2 = 1 := by simp [pow_two]
    rw [h, map_one]
  have hc := hP (j (.sr 0)) (j (.sr 1)) (hs 0) (hs 1)
  have h : (DihedralGroup.sr (0 : ZMod 4)) * .sr 1 = .sr 1 * .sr 0 :=
    hj (by simpa only [map_mul] using hc.eq)
  exact (by decide : ¬ (DihedralGroup.sr (0 : ZMod 4)) * .sr 1 = .sr 1 * .sr 0) h

private def singerCycle : SL := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩
private def singerFrobenius : SL := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

/-- The concrete Singer cycle and Frobenius give a nonidentity seven-element
conjugate to its square in PSL₃(2). -/
theorem exists_seven_conjugate_square :
    ∃ a b : PSL, a ^ 7 = 1 ∧ a ≠ 1 ∧ b * a * b⁻¹ = a ^ 2 := by
  refine ⟨equiv singerCycle, equiv singerFrobenius, ?_, ?_, ?_⟩
  · rw [← map_pow]
    simpa only [map_one] using congrArg equiv (by decide : singerCycle ^ 7 = 1)
  · intro h
    exact (by decide : singerCycle ≠ 1) (equiv.injective (h.trans equiv.map_one.symm))
  · simpa only [map_mul, map_inv, map_pow] using
      congrArg equiv (by decide : singerFrobenius * singerCycle * singerFrobenius⁻¹ =
        singerCycle ^ 2)

end Matrix.PSL3Two
