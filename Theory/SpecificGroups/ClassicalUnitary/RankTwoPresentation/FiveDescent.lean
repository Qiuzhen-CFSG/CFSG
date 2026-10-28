module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCore
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel

/-!
# Canonical projective descent for the unitary five-space

The normal-core calculation traps a Borel-contained normal subgroup in the
scalar kernel. An onto homomorphism to a centerless group kills those scalars,
so its kernel equals the kernel of the literal canonical projective map. The
resulting quotient equivalence commutes with that same map.

This is the central-kernel step in the marked unitary recognition argument;
Bruhat kernel trapping and whole-model generation remain separate premises.
The scalar criterion is the defining projective quotient, with no restriction
on the finite-field parameter (in particular, no specialization to q=4).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
open FivePositive FiveWeyl Theory.SpecificGroups.UnitaryFive
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
variable {Y : Type*} [Group Y]

/-- Onto maps to a centerless group kill exactly the canonical projective
kernel once Bruhat separation traps their kernel in the Borel. -/
theorem kernel_eq_project_kernel (f : J.specialSubgroup →* Y) (hf : Function.Surjective f)
    (hY : Subgroup.center Y=⊥)
    (hB : f.ker≤(roots J κ hκ hJ).borel (h J κ hκ hJ)) : f.ker=(project J).ker := by
  apply le_antisymm (kernel_le_project_kernel J κ hκ hJ f hB)
  intro a ha
  have haZ := project_kernel_le_center J ha
  have hfa : f a∈Subgroup.center Y := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨b,rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp haZ b)
  rw [hY] at hfa
  exact hfa

/-- Descent uses the literal canonical SU₅→PSU₅ map, including its nontrivial
scalar kernel at q=4 and its general-q kernel. -/
def projectiveEquiv (f : J.specialSubgroup →* Y) (hf : Function.Surjective f)
    (hY : Subgroup.center Y=⊥)
    (hB : f.ker≤(roots J κ hκ hJ).borel (h J κ hκ hJ)) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* Y :=
  (QuotientGroup.quotientKerEquivOfSurjective (project J) (project_surjective J)).symm |>.trans
    ((QuotientGroup.quotientMulEquivOfEq (kernel_eq_project_kernel J κ hκ hJ f hf hY hB).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))

@[simp] theorem projectiveEquiv_project (f : J.specialSubgroup →* Y) (hf : Function.Surjective f)
    (hY : Subgroup.center Y=⊥)
    (hB : f.ker≤(roots J κ hκ hJ).borel (h J κ hκ hJ)) (a : J.specialSubgroup) :
    projectiveEquiv J κ hκ hJ f hf hY hB (project J a)=f a := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (project J) (project_surjective J)
  have he : e (QuotientGroup.mk a)=project J a := rfl
  rw [←he]
  change ((QuotientGroup.quotientMulEquivOfEq (kernel_eq_project_kernel J κ hκ hJ f hf hY hB).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)) (e.symm (e (QuotientGroup.mk a)))=f a
  rw [MulEquiv.symm_apply_apply]
  rfl
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
