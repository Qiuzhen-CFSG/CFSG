module

public import Stellmacher.SectionNine.DistanceOneChiefAction
public import Stellmacher.SectionThree.PSetResidualKernel

/-!
# Nontriviality and kernel data for the canonical chief action

The canonical quotient is nontrivial: collapse would put the core-residual
commutator in the initial center, and the generic center-free odd-image
theorem contradicts the branch's noncentral displacement. Thus the actual
residual image is nontrivial. PSet kernel control and the extracted
intersection counts then give order four for the actual U-image, without
assuming that the initial-center kernel acts trivially.

The exact conjugation formula also supplies a kernel criterion and literal
image commutator transport. The initial-center kernel image centralizes the
residual and U images. These facts do not yet identify the two kernels.
Source: Stellmacher (9.1)(10), printed p.47, and (7.7)(a), printed p.36.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem distance_one_chief_core_not_le_subgroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    ¬ q ctx.Γ ctx.criticalPath.a ≤ distanceOneChiefSubgroup ctx.toLocalContext := by
  intro hcollapse
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := pCore 2 P
  let E := twoResidualSubgroup P
  let Z := (z ctx.Γ ctx.criticalPath.a).subgroupOf P
  have hQmap : Q.map P.subtype = q ctx.Γ ctx.criticalPath.a := by
    change twoCoreIn P = q ctx.Γ ctx.criticalPath.a
    exact (ctx.Γ.twoCoreAt_def _).symm
  have hEmap : E.map P.subtype = e ctx.Γ ctx.criticalPath.a := by
    change twoResidualIn P = e ctx.Γ ctx.criticalPath.a
    exact (ctx.Γ.twoResidualAt_def _).symm
  have hQP : q ctx.Γ ctx.criticalPath.a ≤ P := hQmap ▸ Subgroup.map_subtype_le _
  have hZQ := (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
    (distance_one_chief_subgroup_properties ctx.toLocalContext).1
  have hZmap : Z.map P.subtype = z ctx.Γ ctx.criticalPath.a :=
    Subgroup.map_subgroupOf_eq_of_le (hZQ.trans hQP)
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨_, sylow, _⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hcover : E ⊔ (sylow : Subgroup P) = ⊤ := by
    have hcover := twoResidualAmbient_top_sup_sylow sylow
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hcover
    simpa only [E, SectionThree.twoResidualSubgroup_eq_hktPResidual'] using hcover
  have hlocal := (edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨prime, hprime, hoddprime, hpgroup⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 (QuotientGroup.mk' Q)
    (by rw [QuotientGroup.ker_mk'])
  have hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q))) := by
    let _ : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨exponent, hcard⟩ := hpgroup.exists_card_eq
    rw [hcard]
    exact hoddprime.pow
  have hcentral : Z ≤ Subgroup.centralizer (Q : Set P) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hcoreElement
    apply Subtype.ext
    have hZomega := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
      ctx.criticalPath.a ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
    have hmember := (centerAmbient_le_centralizer (q ctx.Γ ctx.criticalPath.a))
      ((omegaOneCenter_le_centerAmbient (q ctx.Γ ctx.criticalPath.a)) (hZomega helement))
    exact Subgroup.mem_centralizer_iff.mp hmember coreElement
      (hQmap ▸ Subgroup.mem_map_of_mem P.subtype hcoreElement)
  have hcomm : ⁅Q, E⁆ ≤ Z := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hQmap, hEmap, hZmap]
    exact (distance_one_le_chief_subgroup_iff ctx.toLocalContext le_rfl).mp hcollapse
  have hQZ := Subgroup.le_of_centerfree_odd_image_commutator_le sylow E Q Z hcover
    (pCore_isPGroup (p := 2) (G := P)) hodd
    (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).start_center_trivial
    hcentral hcomm
  have hbound : q ctx.Γ ctx.criticalPath.a ≤ z ctx.Γ ctx.criticalPath.a := by
    rw [← hQmap, ← hZmap]
    exact Subgroup.map_mono hQZ
  apply branch.noncentral
  exact (Subgroup.commutator_mono hbound le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (branch.le_sylow.trans ((edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.trans
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))))

public theorem distance_one_chief_actor_le_kernel_iff
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D : Subgroup G)
    (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a) :
    D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a) ≤ (distanceOneChiefAction ctx).ker ↔
      ⁅q ctx.Γ ctx.criticalPath.a, D⁆ ≤ distanceOneChiefSubgroup ctx := by
  constructor
  · intro hkernel
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro actor hactor point hpoint
    let actorP : stabilizer ctx.Γ ctx.criticalPath.a := ⟨actor, hDP hactor⟩
    let pointQ : q ctx.Γ ctx.criticalPath.a := ⟨point, hpoint⟩
    have htrivial := MonoidHom.mem_ker.mp (hkernel (show actorP ∈ D.subgroupOf _ from hactor))
    have heq := distance_one_chief_action_apply ctx actorP pointQ
    rw [htrivial] at heq
    have hmem := QuotientGroup.eq_iff_div_mem.mp heq.symm
    change actor * point * actor⁻¹ / point ∈ distanceOneChiefSubgroup ctx at hmem
    simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
  · intro hcomm
    exact Subgroup.quotient_conjugation_action_kills_commutator_layer _ _ _ _ inferInstance
      (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hcomm
      (distanceOneChiefAction ctx) (distance_one_chief_action_apply ctx)

public theorem distance_one_chief_actor_image_commutator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D F : Subgroup G)
    (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hFP : F ≤ stabilizer ctx.Γ ctx.criticalPath.a) :
    ⁅(D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx),
    (F.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx)⁆ =
    (⁅D, F⁆.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx) := by
  rw [← Subgroup.map_commutator]
  congr 1
  apply (Subgroup.map_injective (stabilizer ctx.Γ ctx.criticalPath.a).subtype_injective)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDP,
    Subgroup.map_subgroupOf_eq_of_le hFP,
    Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup D F).trans (sup_le hDP hFP))]

public theorem distance_one_chief_actor_image_eq_bot_of_le_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) (D : Subgroup G)
    (hDQ : D ≤ q ctx.Γ ctx.criticalPath.a) :
    (D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext) = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  exact (Subgroup.subgroupOf_mono _ hDQ).trans
    (distance_one_chief_core_le_action_kernel ctx hb hfaith branch)

public theorem distance_one_initial_center_kernel_image_commutators
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    let P := stabilizer ctx.Γ ctx.criticalPath.a
    let action := distanceOneChiefAction ctx.toLocalContext
    let K := P ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)
    ⁅(K.subgroupOf P).map action,
      ((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map action⁆ = ⊥ ∧
    ⁅(K.subgroupOf P).map action, (branch.U.subgroupOf P).map action⁆ = ⊥ := by
  dsimp only
  have hUE : ⁅branch.U, twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = branch.U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using
      branch.terminal_residual_commutator
  have hdata := distance_one_initial_centralizer_kernel_data ctx hb branch.U
    branch.le_terminal_core hUE
  have hEP : e ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hKP : stabilizer ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) ≤
      stabilizer ctx.Γ ctx.criticalPath.a := inf_le_left
  constructor
  · refine (distance_one_chief_actor_image_commutator ctx.toLocalContext _ _ hKP hEP).trans ?_
    apply distance_one_chief_actor_image_eq_bot_of_le_core ctx hb hfaith branch
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using hdata.2.2.2.1
  · exact (distance_one_chief_actor_image_commutator ctx.toLocalContext _ _ hKP hUP).trans
      (distance_one_chief_actor_image_eq_bot_of_le_core ctx hb hfaith branch _ hdata.2.2.2.2)

public theorem distance_one_chief_residual_actor_image_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    let P := stabilizer ctx.Γ ctx.criticalPath.a
    let action := distanceOneChiefAction ctx.toLocalContext
    ⁅((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map action,
      (branch.U.subgroupOf P).map action⁆ =
      ((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map action := by
  dsimp only
  have hEP : e ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  refine (distance_one_chief_actor_image_commutator ctx.toLocalContext _ _ hEP
    (branch.le_sylow.trans (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1)).trans ?_
  rw [branch.initial_residual_commutator]
  rfl

public theorem distance_one_chief_quotient_nontrivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    Nontrivial (DistanceOneChiefQuotient ctx.toLocalContext) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro htrivial
  let _ := htrivial
  apply distance_one_chief_core_not_le_subgroup ctx branch
  intro element helement
  change (⟨element, helement⟩ : q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a) ∈
    (distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a)
  exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim _ 1)

public theorem distance_one_chief_residual_map_ne_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    ((e ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext) ≠ ⊥ := by
  intro htrivial
  have hEP : e ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hkernel := (Subgroup.map_eq_bot_iff _).mp htrivial
  have hcomm := (distance_one_chief_actor_le_kernel_iff ctx.toLocalContext _ hEP).mp hkernel
  exact distance_one_chief_core_not_le_subgroup ctx branch
    ((Subgroup.le_commutatorPreimage le_rfl hcomm).trans_eq
      (distance_one_chief_second_preimage_eq ctx.toLocalContext))

public theorem distance_one_chief_U_map_card_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card ((branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext)) = 4 := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let action : P →* MulAut (DistanceOneChiefQuotient ctx.toLocalContext) :=
    distanceOneChiefAction ctx.toLocalContext
  have hUP : branch.U ≤ P := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hEsub : (e ctx.Γ ctx.criticalPath.a).subgroupOf P = twoResidualSubgroup P := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  have hres : ¬ twoResidualSubgroup P ≤ action.ker := by
    intro hres
    apply distance_one_chief_residual_map_ne_bot ctx branch
    exact (Subgroup.map_eq_bot_iff _).mpr (hEsub ▸ hres)
  have hindex : (branch.U ⊓ q ctx.Γ ctx.criticalPath.a).relIndex branch.U = 4 := by
    have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
      (branch.U ⊓ q ctx.Γ ctx.criticalPath.a) branch.U bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left, branch.card,
      branch.initial_core_intersection_card] at hcount
    omega
  have hlocal := (edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hlower := SectionThree.pSet_actor_core_index_le_image_card
    T (sectionThreeHypotheses ctx.sectionSeven) P branch.U
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 hUP
    ((sectionThreeHypotheses ctx.sectionSeven).nontrivial_two_subgroup.2.to_le branch.le_sylow)
    action hres
  have hcore : twoCoreAmbient P = q ctx.Γ ctx.criticalPath.a :=
    (ctx.Γ.twoCoreAt_def _).symm
  rw [hcore, hindex] at hlower
  apply le_antisymm _ hlower
  change Nat.card ((branch.U.subgroupOf P).map action) ≤ 4
  rw [← Subgroup.relIndex_ker]
  calc
    action.ker.relIndex (branch.U.subgroupOf P) ≤
        ((q ctx.Γ ctx.criticalPath.a).subgroupOf P).relIndex (branch.U.subgroupOf P) :=
      Subgroup.relIndex_le_of_le_left
        (distance_one_chief_core_le_action_kernel ctx hb hfaith branch)
        (((q ctx.Γ ctx.criticalPath.a).subgroupOf P).subgroupOf
          (branch.U.subgroupOf P)).index_ne_zero_of_finite
    _ = (q ctx.Γ ctx.criticalPath.a).relIndex branch.U := Subgroup.relIndex_subgroupOf hUP
    _ = 4 := by simpa only [Subgroup.inf_relIndex_left] using hindex

end Stellmacher.SectionNine
