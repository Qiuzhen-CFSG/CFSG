module

public import Stellmacher.SectionNine.DistanceOneChiefElementary
public import Stellmacher.SectionNine.DistanceOneChiefQuotientTransport
public import Stellmacher.ResidualCommutatorIdempotence
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The actual action on the canonical initial chief quotient

The initial stabilizer acts by conjugation on Q/C. Residual commutator
idempotence shows that taking its commutator preimage a second time does
not enlarge C. Hence the residual has no fixed points on Q/C. The branch
elementarity result kills the initial core in the action, and the actual
U-displacement has order at most four. No wreath action is assumed here.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem distance_one_stabilizer_normalizes_chief
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    stabilizer ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (distanceOneChiefSubgroup ctx) := by
  have hprops := distance_one_chief_subgroup_properties ctx
  have hQP : q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hprops.1.trans hQP)).mp hprops.2.2.1

public noncomputable def distanceOneChiefAction
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    (stabilizer ctx.Γ ctx.criticalPath.a) →* MulAut (DistanceOneChiefQuotient ctx) :=
  Classical.choose (Subgroup.exists_quotient_conjugation_action
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx) (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a)
    (distance_one_stabilizer_normalizes_chief ctx) inferInstance)

public theorem distance_one_chief_action_apply
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (actor : stabilizer ctx.Γ ctx.criticalPath.a) (point : q ctx.Γ ctx.criticalPath.a) :
    distanceOneChiefAction ctx actor
      (QuotientGroup.mk' ((distanceOneChiefSubgroup ctx).subgroupOf
        (q ctx.Γ ctx.criticalPath.a)) point) =
      QuotientGroup.mk' ((distanceOneChiefSubgroup ctx).subgroupOf (q ctx.Γ ctx.criticalPath.a))
        ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a actor.property) point).mp
              point.property⟩ :=
  Classical.choose_spec (Subgroup.exists_quotient_conjugation_action
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx) (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a)
    (distance_one_stabilizer_normalizes_chief ctx) inferInstance) actor point

public noncomputable def distanceOneChiefActorImage
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D : Subgroup G) :
    Subgroup (MulAut (DistanceOneChiefQuotient ctx)) :=
  (D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx)

public theorem distance_one_chief_second_preimage_eq
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    Subgroup.commutatorPreimage (q ctx.Γ ctx.criticalPath.a) (e ctx.Γ ctx.criticalPath.a)
      (distanceOneChiefSubgroup ctx) = distanceOneChiefSubgroup ctx := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a
  let E := e ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx
  let D := Subgroup.commutatorPreimage Q E C
  have hprops := distance_one_chief_subgroup_properties ctx
  have hQP : Q ≤ P := by
    dsimp only [Q, P]
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPC : P ≤ Subgroup.normalizer C := distance_one_stabilizer_normalizes_chief ctx
  have hQC := hQP.trans hPC
  have hPE : P ≤ Subgroup.normalizer E := by
    dsimp only [P, E]
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  have hPD : P ≤ Subgroup.normalizer D :=
    Subgroup.commutatorPreimage_normalized Q E C P hQC
      (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hPE hPC
  have hQtwo : IsPGroup 2 Q := by
    change IsPGroup 2 (q ctx.Γ ctx.criticalPath.a)
    rw [q, ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hDtwo : IsPGroup 2 D := hQtwo.to_le (Subgroup.commutatorPreimage_le Q E C)
  have hidem : ⁅⁅D, E⁆, E⁆ = ⁅D, E⁆ := by
    simpa only [E, P, CosetGraphContext.e, ctx.Γ.twoResidualAt_def, twoResidualIn,
      stabilizer] using
      commutator_twoResidualAmbient_idempotent D P hDtwo hPD
  have hDC : ⁅D, E⁆ ≤ C := Subgroup.commutator_commutatorPreimage_le Q E C hQC
  have hDZ : ⁅D, E⁆ ≤ z ctx.Γ ctx.criticalPath.a := by
    rw [← hidem]
    exact (Subgroup.commutator_mono hDC le_rfl).trans_eq hprops.2.2.2.1
  refine le_antisymm ((distance_one_le_chief_subgroup_iff ctx
    (Subgroup.commutatorPreimage_le Q E C)).mpr hDZ) ?_
  exact Subgroup.le_commutatorPreimage hprops.1 (hprops.2.2.2.1.le.trans hprops.2.1)

public theorem distance_one_chief_residual_fixed_eq_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    FixedPoints.subgroup (distanceOneChiefActorImage ctx (e ctx.Γ ctx.criticalPath.a))
      (DistanceOneChiefQuotient ctx) = ⊥ := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx
  let E := e ctx.Γ ctx.criticalPath.a
  let projection := QuotientGroup.mk' (C.subgroupOf Q)
  let fixed := FixedPoints.subgroup (distanceOneChiefActorImage ctx E) (DistanceOneChiefQuotient ctx)
  let D := (fixed.comap projection).map Q.subtype
  have hEP : E ≤ P := by
    dsimp only [E, P]
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hDE : ⁅D, E⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    rintro point ⟨representative, hrepresentative, rfl⟩ actor hactor
    let actorP : P := ⟨actor, hEP hactor⟩
    let actorImage : distanceOneChiefActorImage ctx E :=
      ⟨distanceOneChiefAction ctx actorP, Subgroup.mem_map_of_mem _ hactor⟩
    have hfixed := hrepresentative actorImage
    change distanceOneChiefAction ctx actorP (projection representative) =
      projection representative at hfixed
    rw [distance_one_chief_action_apply] at hfixed
    have hmem := QuotientGroup.eq_iff_div_mem.mp hfixed
    have hcomm : ⁅actor, (representative : G)⁆ ∈ C := by
      change actor * (representative : G) * actor⁻¹ / (representative : G) ∈ C at hmem
      simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
    rw [← commutatorElement_inv]
    exact C.inv_mem hcomm
  have hDC : D ≤ C := (Subgroup.le_commutatorPreimage (Subgroup.map_subtype_le _) hDE).trans_eq
    (distance_one_chief_second_preimage_eq ctx)
  apply bot_unique
  intro point hpoint
  obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) point
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hDC (Subgroup.mem_map_of_mem Q.subtype hpoint)

public theorem distance_one_chief_core_le_action_kernel
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    (q ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a) ≤
      (distanceOneChiefAction ctx.toLocalContext).ker := by
  let _ : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.Γ ctx.criticalPath.a)).Normal :=
    distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  let _ : IsElementaryAbelian 2 ((q ctx.Γ ctx.criticalPath.a) ⧸
      (distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf (q ctx.Γ ctx.criticalPath.a)) :=
    distance_one_chief_quotient_elementary ctx hb hfaith branch
  have hcomm : commutator (q ctx.Γ ctx.criticalPath.a) ≤
      (distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf (q ctx.Γ ctx.criticalPath.a) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hbound : ⁅q ctx.Γ ctx.criticalPath.a, q ctx.Γ ctx.criticalPath.a⁆ ≤
      distanceOneChiefSubgroup ctx.toLocalContext := by
    apply Subgroup.commutator_le.mpr
    intro first hfirst second hsecond
    exact hcomm (Subgroup.commutator_mem_commutator
      (show (⟨first, hfirst⟩ : q ctx.Γ ctx.criticalPath.a) ∈ (⊤ : Subgroup _) from trivial)
      (show (⟨second, hsecond⟩ : q ctx.Γ ctx.criticalPath.a) ∈ (⊤ : Subgroup _) from trivial))
  exact Subgroup.quotient_conjugation_action_kills_commutator_layer _ _ _ _ inferInstance
    (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hbound
    (distanceOneChiefAction ctx.toLocalContext) (distance_one_chief_action_apply ctx.toLocalContext)

public theorem distance_one_chief_action_displacement_card_le_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card (commutatorAction (distanceOneChiefActorImage ctx.toLocalContext branch.U)
      (DistanceOneChiefQuotient ctx.toLocalContext)) ≤ 4 := by
  let _ : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.Γ ctx.criticalPath.a)).Normal :=
    distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hcard := Subgroup.quotient_conjugation_commutatorAction_card
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx.toLocalContext) branch.U
    (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hUP inferInstance
    (distanceOneChiefAction ctx.toLocalContext) (distance_one_chief_action_apply ctx.toLocalContext)
  change Nat.card (commutatorAction (distanceOneChiefActorImage ctx.toLocalContext branch.U)
    (DistanceOneChiefQuotient ctx.toLocalContext)) = _ at hcard
  rw [hcard]
  exact (Subgroup.relIndex_le_of_le_left
    (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1
      (((z ctx.Γ ctx.criticalPath.a).subgroupOf
        ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆).index_ne_zero_of_finite)).trans
      (distance_one_chief_displacement_relIndex_bounds ctx branch).2

public theorem distance_one_chief_action_quadratic
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (branch : DistanceOneChiefBranchData ctx) :
    commutatorAction₂ (distanceOneChiefActorImage ctx.toLocalContext branch.U)
      (DistanceOneChiefQuotient ctx.toLocalContext) = ⊥ := by
  let _ : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.Γ ctx.criticalPath.a)).Normal :=
    distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  exact Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx.toLocalContext) branch.U
    (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hUP inferInstance
    ((distance_one_chief_displacement_quadratic ctx hb branch).trans
      (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1)
    (distanceOneChiefAction ctx.toLocalContext) (distance_one_chief_action_apply ctx.toLocalContext)

public theorem distance_one_chief_residual_image_odd_pGroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    ∃ prime : ℕ, prime.Prime ∧ Odd prime ∧ IsPGroup prime
      (distanceOneChiefActorImage ctx.toLocalContext (e ctx.Γ ctx.criticalPath.a)) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  have hcoreker : pCore 2 P ≤ (distanceOneChiefAction ctx.toLocalContext).ker := by
    intro actor hactor
    apply distance_one_chief_core_le_action_kernel ctx hb hfaith branch
    change (actor : G) ∈ q ctx.Γ ctx.criticalPath.a
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hactor
  have hlocal := (edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨prime, hprime, hodd, hgroup⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2
    (distanceOneChiefAction ctx.toLocalContext) hcoreker
  have hEsub : (e ctx.Γ ctx.criticalPath.a).subgroupOf P = twoResidualSubgroup P := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  refine ⟨prime, hprime, hodd, ?_⟩
  change IsPGroup prime (((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map
    (distanceOneChiefAction ctx.toLocalContext))
  rwa [hEsub]

public theorem distance_one_chief_residual_action_full
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    commutatorAction (distanceOneChiefActorImage ctx.toLocalContext (e ctx.Γ ctx.criticalPath.a))
      (DistanceOneChiefQuotient ctx.toLocalContext) = ⊤ := by
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let F := distanceOneChiefActorImage ctx.toLocalContext (e ctx.Γ ctx.criticalPath.a)
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  obtain ⟨prime, hprime, hodd, hgroup⟩ :=
    distance_one_chief_residual_image_odd_pGroup ctx hb hfaith branch
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hcop : Nat.Coprime (Nat.card F) (Nat.card W) := by
    obtain ⟨exponent, heq⟩ := hgroup.exists_card_eq
    obtain ⟨dimension, hdimension⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    change Nat.card F = prime ^ exponent at heq
    rw [heq, hdimension]
    exact (hodd.pow.coprime_two_right).pow_right dimension
  have hsplit : IsCompl (FixedPoints.subgroup F W) (commutatorAction F W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := F)
      (Group.isSolvable_of_comm fun first second => IsMulCommutative.is_comm.comm first second)
      hcop inferInstance
  have hfixed : FixedPoints.subgroup F W = ⊥ :=
    distance_one_chief_residual_fixed_eq_bot ctx.toLocalContext
  have htop := hsplit.sup_eq_top
  rwa [hfixed, bot_sup_eq] at htop

end Stellmacher.SectionNine
