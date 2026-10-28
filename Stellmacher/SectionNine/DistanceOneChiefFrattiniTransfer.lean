module

public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Mathlib.GroupTheory.Frattini

/-!
# The full-actor transfer for the initial chief Frattini subgroup

The normalizer of a subgroup normalizes its ambient Frattini subgroup.
Consequently the latter is normal in the initial vertex stabilizer.
If it centralizes the extracted U modulo the initial center, the equation
[E_initial,U] = E_initial transfers that containment to the full residual.

This is only the transfer in the initial-chief Frattini bound: the actor
containment remains an explicit hypothesis. No initial elementary quotient,
numerical chief recognition, or core equality is used.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem normalizer_le_normalizer_frattiniAmbient
    {G : Type*} [Group G] (core : Subgroup G) :
    Subgroup.normalizer (core : Set G) ≤
      Subgroup.normalizer (FrattiniAmbient core : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  obtain ⟨representative, hrepresentative, rfl⟩ := helement
  let automorphism := Subgroup.normalizerMonoidHom core ⟨actor, hactor⟩
  have hfixed : (frattini core).comap automorphism.toMonoidHom = frattini core :=
    (inferInstance : (frattini core).Characteristic).fixed automorphism
  have himage : automorphism representative ∈ frattini core := by
    change representative ∈ (frattini core).comap automorphism.toMonoidHom
    rwa [hfixed]
  exact ⟨automorphism representative, himage, by
    simp [automorphism, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

public theorem distance_one_chief_frattini_residual_of_actor_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx)
    (hactor : ⁅FrattiniAmbient (q ctx.Γ ctx.criticalPath.a), branch.U⁆ ≤
      z ctx.Γ ctx.criticalPath.a) :
    ⁅FrattiniAmbient (q ctx.Γ ctx.criticalPath.a), e ctx.Γ ctx.criticalPath.a⁆ ≤
      z ctx.Γ ctx.criticalPath.a := by
  let vertexGroup := stabilizer ctx.Γ ctx.criticalPath.a
  let core := q ctx.Γ ctx.criticalPath.a
  let layer := z ctx.Γ ctx.criticalPath.a
  let residual := e ctx.Γ ctx.criticalPath.a
  let frattiniLayer := FrattiniAmbient core
  have hcore : core ≤ vertexGroup := by
    change q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hfrattini : frattiniLayer ≤ vertexGroup :=
    (Subgroup.map_subtype_le _).trans hcore
  have hlayer : layer ≤ vertexGroup :=
    (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
      ((distance_one_chief_subgroup_properties ctx.toLocalContext).1.trans hcore)
  have hresidual : residual ≤ vertexGroup := by
    change e ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact Subgroup.map_subtype_le _
  have hactorGroup : branch.U ≤ vertexGroup :=
    branch.le_sylow.trans (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  let _ : (frattiniLayer.subgroupOf vertexGroup).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a).trans
        (normalizer_le_normalizer_frattiniAmbient core))
  let _ : (layer.subgroupOf vertexGroup).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  have hactor' : ⁅frattiniLayer.subgroupOf vertexGroup,
      branch.U.subgroupOf vertexGroup⁆ ≤ layer.subgroupOf vertexGroup := by
    apply Subgroup.commutator_le.mpr
    intro coreElement hcoreElement actor hactorElement
    exact hactor (Subgroup.commutator_mem_commutator hcoreElement hactorElement)
  have hfull : ⁅residual.subgroupOf vertexGroup,
      branch.U.subgroupOf vertexGroup⁆ = residual.subgroupOf vertexGroup := by
    apply Subgroup.map_injective vertexGroup.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hresidual,
      Subgroup.map_subgroupOf_eq_of_le hactorGroup, branch.initial_residual_commutator]
  have hbound := Subgroup.map_mono (f := vertexGroup.subtype)
    (Subgroup.commutator_le_of_full_actor (frattiniLayer.subgroupOf vertexGroup)
      (residual.subgroupOf vertexGroup) (branch.U.subgroupOf vertexGroup)
      (layer.subgroupOf vertexGroup) hactor' hfull)
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hfrattini,
    Subgroup.map_subgroupOf_eq_of_le hresidual,
    Subgroup.map_subgroupOf_eq_of_le hlayer] at hbound

end Stellmacher.SectionNine
