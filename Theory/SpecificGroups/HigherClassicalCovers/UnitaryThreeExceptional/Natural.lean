module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Mathlib.GroupTheory.IsPerfect

/-!
# The natural SU₄(3) cover retains its full scalar kernel

The scalar matrix iI, where i² = -1 in the concrete nine-element field, is
expressed as a product of three monomial commutators. The four possible
scalar matrices are its powers. Thus every element of the literal projective
kernel lies in the derived subgroup, and perfectness of the projective image
lifts to SU₄(3). The projective perfectness hypothesis is inherited from the
source group; no simplicity certification is needed here.

This supplies the natural cyclic-four factor used by the exceptional-cover
assembly. It makes no assertion about the exceptional three-primary factor.
Source: the canonical factor in GLS3 §6.1, Tables 6.1.2–6.1.3, and
Aschbacher–Smith I.1.4(5), `refs/quasithin.pdf`, printed p.408. The explicit
matrices below prove the needed stem condition directly.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open scoped commutatorElement

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional

private abbrev SU := (UnitaryFourThree.form 4).specialSubgroup
private abbrev Mat := Matrix (Fin 4) (Fin 4) FiniteField.Nine
private def i : FiniteField.Nine := ⟨0, 1⟩

private def makeSU (A : Mat) (hu : A.conjTranspose * A = 1) (hd : A.det = 1) : SU :=
  ⟨⟨A, A.conjTranspose, mul_eq_one_comm.mp hu, hu⟩, by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change A.conjTranspose * 1 * A = 1
      rwa [mul_one]
    · apply Units.ext
      exact hd⟩

private def x₁ : SU := makeSU (diagonal ![i,1,-i,1]) (by decide) (by decide)
private def x₂ : SU := makeSU (diagonal ![-1,-1,1,1]) (by decide) (by decide)
private def y₁ : SU := makeSU
  !![0,0,0,1; 1,0,0,0; 0,0,1,0; 0,1,0,0] (by decide) (by decide)
private def y₂ : SU := makeSU
  !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0] (by decide) (by decide)
private def z : SU := makeSU (diagonal fun _ => i) (by decide) (by decide)

private theorem z_eq_commutators : z = ⁅x₁,y₁⁆ * ⁅x₂,y₂⁆ * ⁅x₁,y₂⁆ := by
  apply Subtype.ext
  apply Units.ext
  decide +kernel

private theorem z_mem_commutator : z ∈ commutator SU := by
  rw [z_eq_commutators]
  exact (commutator SU).mul_mem ((commutator SU).mul_mem
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

/-- Every scalar in the actual projective kernel is a product of commutators.
The fourth-root generator is a product of three explicit monomial commutators. -/
theorem natural_kernel_le_commutator :
    (ProjectiveKernel.project (UnitaryFourThree.form 4)).ker ≤
      commutator (UnitaryFourThree.form 4).specialSubgroup := by
  intro g hg
  obtain ⟨u, hu⟩ := (ProjectiveKernel.scalarKernelEquiv (UnitaryFourThree.form 4)
    (UnitaryFourThree.form_conj_cube 4)).surjective ⟨g, hg⟩
  have hgu : g.val.val = diagonal (fun _ => u.val.val) := by
    have h := congrArg (fun a => a.val.val.val) hu
    exact h.symm
  have hroot : u.val.val ^ 4 = 1 := congrArg Units.val u.property
  have hcases : ∀ t : FiniteField.Nine, t ^ 4 = 1 →
      t = 1 ∨ t = i ∨ t = i ^ 2 ∨ t = i ^ 3 := by decide
  rcases hcases _ hroot with h | h | h | h
  · have he : g = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hgu, h]
      decide
    rw [he]
    exact (commutator SU).one_mem
  · have he : g = z := by
      apply Subtype.ext
      apply Units.ext
      rw [hgu, h]
      rfl
    exact he ▸ z_mem_commutator
  · have he : g = z ^ 2 := by
      apply Subtype.ext
      apply Units.ext
      rw [hgu, h]
      decide
    rw [he]
    exact (commutator SU).pow_mem z_mem_commutator 2
  · have he : g = z ^ 3 := by
      apply Subtype.ext
      apply Units.ext
      rw [hgu, h]
      decide
    rw [he]
    exact (commutator SU).pow_mem z_mem_commutator 3

/-- Perfectness lifts from the source projective group to the natural SU cover,
with all four scalars retained in its derived subgroup. -/
theorem natural_isPerfect [Group.IsPerfect (UnitaryFourThree.Carrier 4)] :
    Group.IsPerfect (UnitaryFourThree.form 4).specialSubgroup := by
  let p := ProjectiveKernel.project (UnitaryFourThree.form 4)
  have hm : (commutator SU).map p = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (ProjectiveKernel.project_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have h := congrArg (Subgroup.comap p) hm
  rw [Subgroup.comap_map_eq, Subgroup.comap_top,
    sup_eq_left.mpr natural_kernel_le_commutator] at h
  exact ⟨h⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional
