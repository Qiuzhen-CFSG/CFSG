module
public import Theory.GroupTheory.Recognition.QuasithinM23.CoreCorrection
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.ConcreteLocal

/-!
# Core-fixing automorphisms of the actual four-pair stabilizer

The original heptad kernel U is abelian and self-centralizing in Ix. The
lifted three-cycle acts fixed-point-freely on U, and UB is the kernel of the
four-set action, hence normal in Ix. The core-conjugation lemma therefore
identifies every automorphism fixing U pointwise with conjugation by U.
All subgroups are the original subgroups of the concrete M23 carrier.

Source: Aschbacher--Smith 5.2.20(5), printed pp.656--657, the equality
C_Aut(Ix)(U) = U used to correct the compatible vertex marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M23Geometry

private abbrev U := heptadKernelAmbient.subgroupOf fourPairStabilizer

private theorem core_le : heptadKernelAmbient ≤ fourPairStabilizer :=
  heptadKernelAmbient_le_twoPair.trans inf_le_left

private def coreEquiv : U ≃* heptadKernel :=
  (subgroupOfEquivOfLe core_le).trans
    (heptadKernel.equivMapOfInjective heptadStabilizer.subtype
      heptadStabilizer.subtype_injective).symm

private theorem coreEquiv_coe (u : U) :
    ((coreEquiv u : heptadStabilizer) : M23) = u.val.val := by
  exact congrArg Subtype.val
    ((heptadKernel.equivMapOfInjective heptadStabilizer.subtype
      heptadStabilizer.subtype_injective).apply_symm_apply _)

private theorem core_selfCentralizing :
    centralizer (U : Set fourPairStabilizer) ≤ U := by
  intro g hg
  have hh : fourPairHeptadInclusion g ∈ centralizer (heptadKernel : Set heptadStabilizer) := by
    apply mem_centralizer_iff.mpr
    intro v hv
    let u := coreEquiv.symm ⟨v,hv⟩
    have hu : ((u : fourPairStabilizer) : M23) = v := by
      rw [←coreEquiv_coe,coreEquiv.apply_symm_apply]
    apply Subtype.ext
    have hc := congrArg Subtype.val ((mem_centralizer_iff.mp hg) u u.property)
    change (u.val.val) * g.val = g.val * u.val.val at hc
    change (v : M23) * g.val = g.val * v
    rw [hu] at hc
    exact hc
  have hh' := heptadKernel_selfCentralizing hh
  exact ⟨fourPairHeptadInclusion g,hh',rfl⟩

private def cubic : fourPairStabilizer :=
  ⟨(AlternatingSection.s AlternatingSection.c : M23), by
    apply (show heptadThreeSubgroup ≤ fourPairStabilizer from
      (show heptadThreeSubgroup ≤ heptadKernelAmbient ⊔ heptadThreeSubgroup from le_sup_right).trans
        (fourTwoPairStabilizer_eq_binary_three ▸ inf_le_left))
    exact mem_zpowers _⟩

private theorem cubic_fixed (u : U) (hu : Commute (u : fourPairStabilizer) cubic) : u = 1 := by
  have huc : Commute u.val.val (cubic : M23) := hu.map fourPairStabilizer.subtype
  have hc : u.val.val ∈ centralizer (heptadThreeSubgroup : Set M23) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    rw [heptadThreeSubgroup_eq_zpowers] at hb
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hb
    exact (huc.zpow_right n).symm.eq
  have hbot : u.val.val ∈ (⊥ : Subgroup M23) :=
    heptadKernelAmbient_inf_centralizer_three ▸ (show
      u.val.val ∈ heptadKernelAmbient ⊓ centralizer (heptadThreeSubgroup : Set M23)
      from ⟨u.property,hc⟩)
  apply Subtype.ext
  apply Subtype.ext
  exact mem_bot.mp hbot

private theorem cubic_core_normal : (U ⊔ zpowers cubic).Normal := by
  let f : fourPairStabilizer →* Equiv.Perm lambda :=
    (setAction lambda).comp (inclusion (show fourPairStabilizer ≤ fourStabilizer from inf_le_left))
  have he : U ⊔ zpowers cubic = f.ker := by
    have hm : (U ⊔ zpowers cubic).map fourPairStabilizer.subtype = fourKernelAmbient := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le core_le,MonoidHom.map_zpowers]
      change heptadKernelAmbient ⊔ zpowers
        (AlternatingSection.s AlternatingSection.c : M23) = fourKernelAmbient
      rw [←heptadThreeSubgroup_eq_zpowers,←fourKernelAmbient_eq_binary_three]
    apply map_injective fourPairStabilizer.subtype_injective
    rw [hm]
    ext g
    constructor
    · intro hg
      have hgI := fourKernelAmbient_le_twoPair hg |>.1
      refine ⟨⟨g,hgI⟩,?_,rfl⟩
      exact (mem_setAction_ker lambda _).mpr ((mem_fourKernelAmbient g).mp hg)
    · rintro ⟨g,hg,rfl⟩
      apply (mem_fourKernelAmbient _).mpr
      exact (mem_setAction_ker lambda _).mp hg
  rw [he]
  infer_instance

/-- The pointwise automorphism fixer of the actual sixteen-core in Ix
consists of conjugations by that same core. -/
theorem fourPair_core_fixing_inner (α : MulAut fourPairStabilizer)
    (hα : ∀ u : heptadKernelAmbient.subgroupOf fourPairStabilizer, α u = u) :
    ∃ u : heptadKernelAmbient.subgroupOf fourPairStabilizer,
      α = MulAut.conj (u : fourPairStabilizer) := by
  apply QuasithinM23.exists_core_conjugator U
    (fun u v => coreEquiv.injective (by simp only [map_mul]; exact heptadKernel_mul_comm _ _))
    core_selfCentralizing cubic cubic_fixed cubic_core_normal α hα

end Sporadic.Mathieu.M23Geometry
