module

public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Stellmacher.SectionNine.DistanceOneChiefFrattiniTransfer
public import Stellmacher.SectionNine.DistanceOneChiefTerminalProduct
public import Theory.GroupAction.QuotientConjugationFrattiniLayer
public import Theory.GroupAction.Extraspecial27FrattiniDisplacement

/-!
# The initial chief Frattini residual bound

The actual extracted subgroup U has an elementary terminal-center quotient
of order64 with extraspecial27 residual action. The initial two-core acts
on this quotient through a two-group normalizing that residual image. It
commutes with the selected initial-center involution and fixes its
displacement pointwise. The proved extraspecial Frattini displacement
theorem therefore bounds its Frattini action by that displacement.

The prescribed quotient action transports this bound back to
[FrattiniAmbient Q_initial,U] ≤ Z_initial. Normality of the Frattini
subgroup in the initial stabilizer and [E_initial,U] = E_initial then
give the residual bound. No identification of the initial center kernel
with the core, initial elementary quotient, chief cardinality, or core
equality is used.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.47 / PDF p.37,
the large terminal action immediately before relation (10).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_chief_frattini_commutator_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    ⁅FrattiniAmbient (q ctx.Γ ctx.criticalPath.a), e ctx.Γ ctx.criticalPath.a⁆ ≤
      z ctx.Γ ctx.criticalPath.a := by
  rcases hfaith with ⟨_, _⟩
  have hterminalResidual :
      ⁅branch.U, twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = branch.U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using
      branch.terminal_residual_commutator
  obtain ⟨hnormal, helementary, hcard, hquotientCard, hnontrivial, hnormalizes,
      action, haction, hkernel, hfull, distinguished, hdistinguished, hinvolution,
      houtside, himageInvolution, hgenerates, hindex, hcenter, hodd, hoddCard⟩ :=
    distance_one_large_v1_quotient_action ctx hb branch.U branch.le_terminal_core
      branch.terminal_center_le branch.terminal_core_commutator hterminalResidual
      branch.le_sylow branch.normal_in_sylow branch.action_nontrivial branch.action_upper
      branch.noncentral
  let _ := hnormal
  let _ := helementary
  let vertexGroup := stabilizer ctx.Γ ctx.criticalPath.a'
  let core := q ctx.Γ ctx.criticalPath.a
  let layer := z ctx.Γ ctx.criticalPath.a
  let kernel := z ctx.Γ ctx.criticalPath.a'
  let W := branch.U ⧸ kernel.subgroupOf branch.U
  let oddGroup := ((twoResidualIn vertexGroup).subgroupOf vertexGroup).map action
  let actors := (core.subgroupOf vertexGroup).map action
  have hstep : ctx.criticalPath.firstStep = ctx.criticalPath.a' := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb.symm
  have hneighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [← hstep]
    exact (mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  have hcoreSylow : core ≤ T :=
    (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hSylowVertex : T ≤ vertexGroup := by
    change T ≤ stabilizer ctx.Γ ctx.criticalPath.a'
    rw [← hstep]
    exact (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1
  have hcoreVertex : core ≤ vertexGroup := hcoreSylow.trans hSylowVertex
  have hlayerCenter : layer ≤ omegaOneCenter core :=
    (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hneighbor
  have hcoreLayer : core ≤ Subgroup.centralizer (layer : Set G) :=
    Subgroup.le_centralizer_iff.mp (hlayerCenter.trans
      ((omegaOneCenter_le_centerAmbient core).trans (centerAmbient_le_centralizer core)))
  have hactedLayer : branch.U ≤ Subgroup.normalizer (layer : Set G) :=
    (branch.le_sylow.trans
      (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1).trans
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  have hkernelLayer : kernel ≤ layer :=
    distance_one_terminal_center_le_initial_center ctx.toLocalContext hb
  have hcoreTwo : IsPGroup 2 core := by
    change IsPGroup 2 (q ctx.Γ ctx.criticalPath.a)
    rw [q, ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer ctx.Γ ctx.criticalPath.a)).map _
  have hactorsTwo : IsPGroup 2 actors :=
    (hcoreTwo.of_equiv (Subgroup.subgroupOfEquivOfLe hcoreVertex).symm).map action
  let _ : ((twoResidualIn vertexGroup).subgroupOf vertexGroup).Normal :=
    twoResidualIn_normal vertexGroup
  have hactorsNormalizes : actors ≤ Subgroup.normalizer (oddGroup : Set (MulAut W)) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actor ⟨actorLift, hactorLift, rfl⟩ element ⟨elementLift, helementLift, rfl⟩
    refine ⟨actorLift * elementLift * actorLift⁻¹,
      Subgroup.Normal.conj_mem (inferInstance :
        ((twoResidualIn vertexGroup).subgroupOf vertexGroup).Normal)
        elementLift helementLift actorLift, ?_⟩
    simp only [map_mul, map_inv]
  have hdistinguishedCore : (distinguished : G) ∈ core :=
    (hlayerCenter.trans (Subgroup.map_subtype_le _)) hdistinguished
  let involution : actors :=
    ⟨action distinguished, Subgroup.mem_map_of_mem action hdistinguishedCore⟩
  obtain ⟨hdisplacementLayer, hcommutes, hfixes⟩ :=
    Subgroup.quotient_conjugation_centralizing_actor_data vertexGroup branch.U kernel layer
      core hnormalizes hnormal hactedLayer hcoreLayer action haction distinguished
      hdistinguished
  have hbound := extraspecial27_frattini_displacement_le oddGroup actors hodd hoddCard hquotientCard
    hfull hactorsTwo hactorsNormalizes involution himageInvolution hgenerates hcenter hindex
    (fun actor => hcommutes actor actor.property)
    (fun actor point hpoint => hfixes actor actor.property point (hdisplacementLayer hpoint))
  apply distance_one_chief_frattini_residual_of_actor_bound ctx branch
  exact Subgroup.commutator_frattini_le_of_quotient_action vertexGroup branch.U kernel layer
    core hnormalizes hnormal hkernelLayer hcoreVertex action haction
      (hbound.trans hdisplacementLayer)

end Stellmacher.SectionNine
