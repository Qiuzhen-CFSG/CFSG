module
public import Theory.SpecificGroups.LieType.F4RootSL2
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry

/-!
# Faithfulness of the F4 symplectic subsystem after central projection

A central element in a symplectic matrix group is scalar. Preserving one
hyperbolic pair makes the scalar square to one, so the only possibilities
in degree six are the identity and the negative identity. Consequently a
faithful map to the F4 elementary group can acquire no central kernel if
its negative identity equals the long-root SL2 involution: that involution
is already proved noncentral by an explicit neighboring-root calculation.

This argument avoids a centerlessness theorem for the full elementary F4
group. `F4RootCentralizer.residualEquivOfFaithfulSubsystem` applies it to the
actual central quotient, including in characteristic three. The explicit
symplectic matrix representation and involution identity remain the
construction inputs; neither is supplied by this lemma.

Source: the central-product qualification in the fundamental-subgroup
centralizer used in Aschbacher–Smith A.2.17, printed p.39 of
`refs/quasithin.pdf`; GLS3 §2.6 for subsystem versions. The scalar argument
reuses the attributed ATLAS adaptation in `PSp4Three.ProjectiveGeometry`.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootCentralizer
open Matrix
open scoped MatrixGroups
open F4RootSL2
variable {F : Type*} [Field F]

/-- The actual negative identity matrix in Sp6. -/
def symplecticNegOne : Matrix.symplecticGroup (Fin 3) F :=
  ⟨-1, SymplecticGroup.neg_mem (Submonoid.one_mem _)⟩

/-- Its underlying matrix is exactly minus the identity. -/
@[simp] theorem symplecticNegOne_val :
    (symplecticNegOne (F := F)).val = -1 := rfl

private theorem symplectic_center_cases (x : Matrix.symplecticGroup (Fin 3) F)
    (hx : x ∈ Subgroup.center (Matrix.symplecticGroup (Fin 3) F)) :
    x = 1 ∨ x = symplecticNegOne := by
  obtain ⟨a, ha⟩ := Matrix.PSp4Three.central_is_scalar (n := 3) (F := F) x hx
  have hp := Matrix.PSp4Three.preserves (n := 3) (F := F) x (Matrix.PSp4Three.e 0)
    (Matrix.PSp4Three.f 0)
  have hvec (v : Matrix.PSp4Three.Vector 3 F) : x.val *ᵥ v = a • v :=
    (Matrix.PSp4Three.smul_eq_mulVec x v).symm.trans (ha v)
  rw [hvec, hvec] at hp
  have ha2 : a ^ 2 = 1 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      Matrix.PSp4Three.form_f_right, Matrix.PSp4Three.e, Pi.single_eq_same,
      mul_one, pow_two] using hp
  rcases sq_eq_one_iff.mp ha2 with rfl | rfl
  · left
    apply Matrix.PSp4Three.ext_action
    intro v
    simpa using ha v
  · right
    apply Matrix.PSp4Three.ext_action
    intro v
    rw [ha]
    rw [Matrix.PSp4Three.smul_eq_mulVec]
    simp [symplecticNegOne, Matrix.neg_mulVec]

/-- A faithful symplectic realization matching the long-root involution
remains faithful under the defining central projection of F4. -/
theorem central_kernel_of_faithful_neg_one
    (hF : (2 : F) ≠ 0)
    (f : Matrix.symplecticGroup (Fin 3) F →* Elementary F)
    (hinj : Function.Injective f)
    (hneg : f symplecticNegOne = elementaryHom (-1 : SL(2, F)))
    (x : Matrix.symplecticGroup (Fin 3) F)
    (hx : f x ∈ Subgroup.center (Elementary F)) : x = 1 := by
  have hc : x ∈ Subgroup.center (Matrix.symplecticGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hinj
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hx (f y)
  rcases symplectic_center_cases x hc with h | rfl
  · exact h
  · rw [hneg] at hx
    exact (elementaryHom_neg_one_not_mem_center hF hx).elim

end ExceptionalSplit.F4RootCentralizer
end
