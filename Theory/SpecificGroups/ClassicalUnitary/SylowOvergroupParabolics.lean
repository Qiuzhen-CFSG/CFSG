module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.LinearAlgebra.FiniteProjectiveMatrixGroup
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Projective unitary subspace stabilizers

The stabilizer of a subspace is formed inside the actual special unitary
matrix group and then mapped by its canonical projection into PGL. Scalar
matrices preserve every subspace, so the inverse image of this projective
stabilizer is exactly the original stabilizer. Nonzero totally isotropic
subspaces specify the maximal geometric parabolics.

These definitions extend the construction in `ClassicalUnitary.FiveFlag`
to arbitrary dimensions and Hermitian forms. They supply the common geometry
for the placement and radical calculations used in the proper Sylow-overgroup
argument; neither calculation is assumed by the definitions.

Source: GLS3, §§2.6--2.7, especially 2.6.4--2.6.5, and Aschbacher--Smith
B.1.13, printed p.74 (PDF p.85).
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix Subgroup
open scoped Pointwise

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics

variable {F : Type*} [Field F] {d : ℕ}

/-- Total isotropy for the stored Hermitian matrix and involution. -/
def TotallyIsotropic (J : HermitianForm d F) (W : Submodule F (Fin d → F)) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, dotProduct (fun i => J.conj (v i)) (J.form.mulVec w) = 0

/-- The actual SU-to-PSU projection, with PSU defined as an image in PGL. -/
def project (J : HermitianForm d F) :
    J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun a => ⟨a.val, a.property, rfl⟩)

theorem project_surjective (J : HermitianForm d F) :
    Function.Surjective (project J) := by
  rintro ⟨x, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

/-- The natural linear action before taking the projective image. -/
def linearAction (J : HermitianForm d F) :
    J.specialSubgroup →* ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F)).toMonoidHom.comp
    GeneralLinearGroup.toLin.toMonoidHom).comp J.specialSubgroup.subtype

/-- The exact special unitary stabilizer of a subspace. -/
def specialStabilizer (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    Subgroup J.specialSubgroup :=
  (MulAction.stabilizer ((Fin d → F) ≃ₗ[F] (Fin d → F)) W).comap (linearAction J)

theorem mem_specialStabilizer_iff (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) (A : J.specialSubgroup) :
    A ∈ specialStabilizer J W ↔
      ∀ v, (A.val : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ W ↔ v ∈ W := by
  change linearAction J A ∈ MulAction.stabilizer _ W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

/-- The projective subspace stabilizer; for a nonzero totally isotropic
subspace this is the corresponding maximal geometric parabolic. -/
def parabolic (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (specialStabilizer J W).map (project J)

theorem ker_project_le_specialStabilizer (J : HermitianForm d F)
    (W : Submodule F (Fin d → F)) : (project J).ker ≤ specialStabilizer J W := by
  intro A hA
  have h : ProjGenLinGroup.mk A.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hA)
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  rw [mem_specialStabilizer_iff]
  intro v
  rw [← hu]
  change (Matrix.diagonal (fun _ : Fin d => u.val)) *ᵥ v ∈ W ↔ v ∈ W
  rw [Matrix.diagonal_const_mulVec]
  exact W.smul_mem_iff u.ne_zero

/-- The projective convention loses no stabilizer information on pulling back. -/
theorem comap_parabolic (J : HermitianForm d F) (W : Submodule F (Fin d → F)) :
    (parabolic J W).comap (project J) = specialStabilizer J W := by
  apply le_antisymm
  · rintro A ⟨B, hB, hBA⟩
    have hk : B⁻¹ * A ∈ (project J).ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hBA, inv_mul_cancel]
    have h := (specialStabilizer J W).mul_mem hB
      (ker_project_le_specialStabilizer J W hk)
    simpa only [mul_inv_cancel_left] using h
  · intro A hA
    exact ⟨A, hA, rfl⟩

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
