module
public import Theory.GroupTheory.OddPrimeSectionCentralizers
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.OddKernelCenter

/-!
# The kernel of the supercritical quotient action

For a cover with three-group kernel, the target's self-centralizing
three-core makes the covering three-core self-centralizing. Conjugation
on a supercritical Frattini quotient then has three-group kernel, hence
kernel contained in the covering three-core. These are the literal
conjugation maps used in the proof of A.1.31(3), printed pp.27--28.
-/

public section
open Subgroup
namespace Theory.GroupTheory.ThreeSection
variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

/-- Self-centralization of the target three-core lifts through a three-kernel. -/
theorem source_core_selfCentralizing (f : D →* E) (hf : Function.Surjective f)
    (hk : IsPGroup 3 f.ker) (hF : generalizedFitting E = pCore 3 E) :
    centralizer (pCore 3 D : Set D) ≤ pCore 3 D := by
  have hpre := f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore 3 D).map f = pCore 3 E := by
    rw [← hpre, map_comap_eq_self_of_surjective hf]
  have hE : centralizer (pCore 3 E : Set E) ≤ pCore 3 E := by
    simpa only [hF] using centralizer_generalizedFitting_le E
  intro x hx
  rw [← hpre]
  apply hE
  rw [← hmap]
  exact map_centralizer_le_centralizer_image _ f (mem_map_of_mem f hx)

/-- The action on the supercritical Frattini quotient has kernel inside
the original three-core, using its actual conjugation action. -/
theorem supercritical_action_kernel_le_core
    (hc : centralizer (pCore 3 D : Set D) ≤ pCore 3 D)
    (X : Subgroup (pCore 3 D)) (hX : IsSupercriticalPSubgroup 3 X) :
    letI : X.Characteristic := hX.characteristic
    (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (MulAut.conjNormal : D →* MulAut (pCore 3 D))).ker ≤ pCore 3 D := by
  let : X.Characteristic := hX.characteristic
  let a : D →* MulAut (pCore 3 D) := MulAut.conjNormal
  have ha : IsPGroup 3 a.ker := by
    apply pCore_isPGroup.to_le
    intro x hx
    apply hc
    intro y hy
    have he := congrArg (fun b : MulAut (pCore 3 D) => (b ⟨y, hy⟩ : D)) hx
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let α := ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp a
  have hα : IsPGroup 3 α.ker :=
    (hX.isPGroup_frattini_action_kernel pCore_isPGroup (by decide : Odd 3)).comap_of_ker_isPGroup a ha
  exact le_sSup ⟨inferInstance, hα⟩

end Theory.GroupTheory.ThreeSection
