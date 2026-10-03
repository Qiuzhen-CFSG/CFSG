module

public import Stellmacher.SectionEight.GeneratedEightSixNextCoreStructure
public import Stellmacher.SectionEight.GeneratedEightSixNextVGeometry
public import Stellmacher.ResidualCommutatorIdempotence
public import Stellmacher.ResidualCoreCommutator
public import Stellmacher.SectionFiveToSeven.LocalResidualCoreContainment
public import Theory.GroupTheory.NormalCenterQuotient
public import Stellmacher.C4QuaternionResidualAction

/-!
# NextCoreResidual in the small-index branch of (8.6)

The graph-local small-index argument is assembled from the proved local order and action
calculations.

The graph-local form takes `SectionEightLocalContext`; the original generated-context
theorem remains a wrapper with its statement and name unchanged.

Source: Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement

universe u

public theorem eight_six_closure_eq_seed_sup_residual_commutator
    {G : Type u} [Group G] (seed actors residual cover whole : Subgroup G)
    (hresidual : residual ≤ actors) (hcover : cover ≤ actors)
    (hnormal : (residual.subgroupOf actors).Normal)
    (hsupplement : residual ⊔ cover = actors)
    (hcoverSeed : cover ≤ Subgroup.normalizer (seed : Set G))
    (hseed : seed ≤ whole)
    (hwhole : actors ≤ Subgroup.normalizer (whole : Set G))
    (hclosure : whole = conjugateClosure seed actors) :
    whole = seed ⊔ ⁅whole, residual⁆ := by
  have hcomm : ⁅whole, residual⁆ ≤ whole :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hresidual.trans hwhole)
  apply le_antisymm
  · conv_lhs => rw [hclosure]
    rw [conjugateClosure, Subgroup.closure_le]
    rintro element ⟨actor, representative, rfl⟩
    have hsupplement' : residual.subgroupOf actors ⊔ cover.subgroupOf actors = ⊤ := by
      apply Subgroup.map_injective actors.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hresidual,
        Subgroup.map_subgroupOf_eq_of_le hcover, hsupplement,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    let _ : (residual.subgroupOf actors).Normal := hnormal
    have hactor : actor ∈ residual.subgroupOf actors ⊔ cover.subgroupOf actors := by
      rw [hsupplement']
      trivial
    obtain ⟨first, hfirst, second, hsecond, hfactor⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hactor
    have hpoint : (second : G) * representative * (second : G)⁻¹ ∈ seed :=
      (Subgroup.mem_normalizer_iff.mp (hcoverSeed hsecond) representative).mp
        representative.property
    have hchange : ⁅(first : G), (second : G) * representative * (second : G)⁻¹⁆ ∈
        ⁅whole, residual⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hfirst (hseed hpoint)
    have hproduct := (seed ⊔ ⁅whole, residual⁆).mul_mem
      ((show ⁅whole, residual⁆ ≤ seed ⊔ ⁅whole, residual⁆ from le_sup_right) hchange)
      ((show seed ≤ seed ⊔ ⁅whole, residual⁆ from le_sup_left) hpoint)
    have hfactor' : (actor : G) = (first : G) * (second : G) :=
      (congrArg Subtype.val hfactor).symm
    change (actor : G) * representative * (actor : G)⁻¹ ∈ _
    rw [hfactor']
    convert hproduct using 1
    simp [commutatorElement_def, mul_assoc]
  · exact sup_le hseed hcomm

public theorem eight_six_next_v_eq_seed_sup_residual_commutator_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2) :
    VAt ctx.Γ ctx.criticalPath.firstStep = ZAt ctx.Γ ctx.criticalPath.a ⊔
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ := by
  have hedge := SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hback : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  apply eight_six_closure_eq_seed_sup_residual_commutator _
    (GAt ctx.Γ ctx.criticalPath.firstStep) _ S
  · change ctx.Γ.twoResidualAt _ ≤ ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact SevenSix.twoResidualIn_le _
  · exact hedge.2.1
  · change ((ctx.Γ.twoResidualAt _).subgroupOf (ctx.Γ.vertexStabilizer _)).Normal
    rw [ctx.Γ.twoResidualAt_def]
    exact SevenSix.twoResidualIn_normal _
  · change ctx.Γ.twoResidualAt _ ⊔ S = ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact SevenSix.twoResidualIn_sup_sylow hedge.2
  · exact hedge.1.1.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  · exact (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  · exact stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
  · exact eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a hback

public theorem eight_six_next_residual_commutator_not_le_line_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ¬ ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hle
  have hline := (eight_six_first_step_fixed_line_local ctx hcenter hcard).2
  have hcollapse : VAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    rw [eight_six_next_v_eq_seed_sup_residual_commutator_local ctx]
    exact sup_le le_rfl (hle.trans hline)
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hfirst
  have hcomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  exact eight_six_next_v_noncommutative_local ctx hlength
    (le_bot_iff.mp ((Subgroup.commutator_mono hcollapse hcollapse).trans hcomm.le))

public theorem eight_six_next_residual_commutator_properties_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2) :
    let whole := VAt ctx.Γ ctx.criticalPath.firstStep
    let residual := EAt ctx.Γ ctx.criticalPath.firstStep
    ⁅whole, residual⁆ ≤ whole ∧
      ⁅whole, residual⁆ ≤ QAt ctx.Γ ctx.criticalPath.firstStep ⊓ residual ∧
      ⁅⁅whole, residual⁆, residual⁆ = ⁅whole, residual⁆ := by
  dsimp only
  have hwholeCore := SevenSix.neighbor_join_le_core_of_length_gt_one
    ctx.Γ ctx.criticalPath (by omega) ctx.criticalPath.firstStep
  have hresidual : EAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoResidualAt _ ≤ ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact SevenSix.twoResidualIn_le _
  refine ⟨Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hresidual.trans (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep)), ?_, ?_⟩
  · rw [eight_six_next_residual_intersection_eq_core]
    have hbound := Subgroup.commutator_mono hwholeCore
      (show EAt ctx.Γ ctx.criticalPath.firstStep ≤ EAt ctx.Γ ctx.criticalPath.firstStep
        from le_rfl)
    apply hbound.trans
    rw [Subgroup.commutator_comm]
    change ⁅ctx.Γ.twoResidualAt _, ctx.Γ.twoCoreAt _⁆ ≤
      twoCoreIn (ctx.Γ.twoResidualAt _)
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def]
    exact SevenSix.residual_commutator_core_le _
  · have hcorep : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.firstStep) := by
      change IsPGroup 2 (ctx.Γ.twoCoreAt _)
      rw [ctx.Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    have haction := commutator_twoResidualAmbient_idempotent
      (VAt ctx.Γ ctx.criticalPath.firstStep) (GAt ctx.Γ ctx.criticalPath.firstStep)
      (hcorep.to_le hwholeCore) (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep)
    change ⁅⁅VAt ctx.Γ ctx.criticalPath.firstStep, ctx.Γ.twoResidualAt _⁆,
      ctx.Γ.twoResidualAt _⁆ = ⁅VAt ctx.Γ ctx.criticalPath.firstStep, ctx.Γ.twoResidualAt _⁆
    rw [ctx.Γ.twoResidualAt_def]
    exact haction

public theorem eight_six_commutator_le_of_normal_small_index
    {G : Type u} [Group G] [Finite G] (core whole : Subgroup G)
    [core.Normal] [whole.Normal] (hle : whole ≤ core)
    (hcard : Nat.card core ≤ 2 * Nat.card whole) :
    ⁅core, (⊤ : Subgroup G)⁆ ≤ whole := by
  let projection := QuotientGroup.mk' whole
  let image := core.map projection
  have hindex : Nat.card image ≤ 2 := by
    have hratio := (whole.subgroupOf core).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hratio
    have hcardImage : Nat.card image = (whole.subgroupOf core).index := by
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
      rfl
    rw [hcardImage]
    nlinarith [Nat.card_pos (α := whole)]
  have hcentral : image ≤ Subgroup.center (G ⧸ whole) := by
    by_cases hone : Nat.card image = 1
    · rw [Subgroup.card_eq_one.mp hone]
      exact bot_le
    · have htwo : Nat.card image = 2 := by
        have := Nat.card_pos (α := image)
        omega
      exact Subgroup.central_of_normal_card_two image htwo
  have hcomm : ⁅image, (⊤ : Subgroup (G ⧸ whole))⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hcentral
  have hzero : (⁅core, (⊤ : Subgroup G)⁆).map projection = ⊥ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective projection (QuotientGroup.mk'_surjective whole)]
    exact hcomm
  simpa only [projection, QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff (f := projection) _).mp hzero

public theorem eight_six_next_core_commutator_le_v_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (hbound : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) ≤ 32)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8) :
    ⁅QAt ctx.Γ ctx.criticalPath.firstStep, GAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let actors := GAt ctx.Γ ctx.criticalPath.firstStep
  let core := QAt ctx.Γ ctx.criticalPath.firstStep
  let whole := VAt ctx.Γ ctx.criticalPath.firstStep
  have hcore : core ≤ actors := by
    change ctx.Γ.twoCoreAt _ ≤ ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hwholeCore : whole ≤ core := SevenSix.neighbor_join_le_core_of_length_gt_one
    ctx.Γ ctx.criticalPath (by omega) ctx.criticalPath.firstStep
  have hwhole := hwholeCore.trans hcore
  let _ : (core.subgroupOf actors).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hcore).mpr
    exact SevenSix.stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.firstStep
  let _ : (whole.subgroupOf actors).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hwhole).mpr
    exact stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
  have hnative := eight_six_commutator_le_of_normal_small_index
    (core.subgroupOf actors) (whole.subgroupOf actors)
    (Subgroup.subgroupOf_mono actors hwholeCore) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcore).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hwhole).toEquiv]
      have hcard := eight_six_c4_quaternion_card hv
      change Nat.card whole = 16 at hcard
      change Nat.card core ≤ 32 at hbound
      omega)
  have hmapped := Subgroup.map_mono (f := actors.subtype) hnative
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hcore,
    Subgroup.map_subgroupOf_eq_of_le hwhole,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapped

public theorem eight_six_next_residual_intersection_eq_commutator_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (hbound : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) ≤ 32)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8) :
    QAt ctx.Γ ctx.criticalPath.firstStep ⊓ EAt ctx.Γ ctx.criticalPath.firstStep =
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ := by
  let residual := EAt ctx.Γ ctx.criticalPath.firstStep
  let residualCore := twoCoreIn residual
  have hback : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  have hodd : Odd (Nat.card (residual ⧸ pCore 2 residual)) := by
    have hlocal := local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a hback
      (GAt ctx.Γ ctx.criticalPath.firstStep) le_rfl
    change Odd (Nat.card (ctx.Γ.twoResidualAt _ ⧸ pCore 2 (ctx.Γ.twoResidualAt _)))
    rw [ctx.Γ.twoResidualAt_def]
    exact hlocal
  have hperfect : BenderSuzuki.External.hktPResidual 2 residual = ⊤ := by
    change BenderSuzuki.External.hktPResidual 2 (ctx.Γ.twoResidualAt _) = ⊤
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualAmbient_has_top_twoResidual _
  have hfull : residualCore = ⁅residualCore, residual⁆ := by
    have hmapped := congrArg (Subgroup.map residual.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmapped
    exact hmapped
  have hcore : residualCore ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
    change twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤ _
    rw [← eight_six_next_residual_intersection_eq_core]
    exact inf_le_left
  have hresidual : residual ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoResidualAt _ ≤ ctx.Γ.vertexStabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact SevenSix.twoResidualIn_le _
  have hcoreV : residualCore ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [hfull]
    exact (Subgroup.commutator_mono hcore hresidual).trans
      (eight_six_next_core_commutator_le_v_local ctx hlength hbound hv)
  apply le_antisymm
  · rw [eight_six_next_residual_intersection_eq_core]
    change residualCore ≤ _
    rw [hfull]
    exact Subgroup.commutator_mono hcoreV le_rfl
  · exact (eight_six_next_residual_commutator_properties_local ctx hlength).2.1

set_option linter.unusedVariables false in
public theorem eight_six_next_residual_action_inputs_of_small_v_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4)) :
    (QAt ctx.Γ ctx.criticalPath.firstStep ⊓ EAt ctx.Γ ctx.criticalPath.firstStep =
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
        twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)⁆) ∧
    GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) ∧
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≠ ⊥ := by
  have hbound : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) ≤ 32 := by
    rcases eight_six_next_core_card_local ctx.sectionSeven ctx.Γ ctx.criticalPath
      orders hquot hcard hnext with hsmallCore | hlargeCore <;> omega
  have hequal := eight_six_next_residual_intersection_eq_commutator_local
    ctx hlength hbound hv
  have hnoncentral := eight_six_next_residual_commutator_not_le_line_local
    ctx hcenter hlength hcard
  have hresidual : EAt ctx.Γ ctx.criticalPath.firstStep =
      twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep) := by
    change ctx.Γ.twoResidualAt _ = _
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  change QAt ctx.Γ ctx.criticalPath.firstStep ⊓ EAt ctx.Γ ctx.criticalPath.firstStep =
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, EAt ctx.Γ ctx.criticalPath.firstStep⁆ at hequal
  rw [hresidual] at hequal
  refine ⟨?_, stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep, ?_⟩
  · simpa only [hresidual] using hequal
  · intro hzero
    apply hnoncentral
    rw [hresidual, hzero]
    exact bot_le

public theorem generated_eight_six_next_residual_action_inputs_of_small_v
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4)) :
    (QAt ctx.Γ ctx.criticalPath.firstStep ⊓ EAt ctx.Γ ctx.criticalPath.firstStep =
      ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
        twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)⁆) ∧
    GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set (P1 ⊔ P2 : Subgroup H)) ∧
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≠ ⊥ := by
  exact eight_six_next_residual_action_inputs_of_small_v_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall hv hi


set_option linter.unusedVariables false in
public theorem eight_six_next_residual_intersection_model_of_small_v_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : Later.SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup G)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4)) :
    IsModel (QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      EAt ctx.Γ ctx.criticalPath.firstStep) Q8 := by
  obtain ⟨hequal, hnormalize, hnontrivial⟩ :=
    eight_six_next_residual_action_inputs_of_small_v_local ctx hcenter hquot
      hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall hv hi
  rw [hequal]
  exact c4_quaternion_nontrivial_residual_commutator_model
    (VAt ctx.Γ ctx.criticalPath.firstStep) (GAt ctx.Γ ctx.criticalPath.firstStep)
    hv hnormalize hnontrivial

public theorem generated_eight_six_next_residual_intersection_model_of_small_v
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : Later.GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hbase : ⁅D,L⁆ = ZAt ctx.Γ ctx.criticalPath.a ∧
      QuotientIsElementaryAbelian Q D 2 ∧ IsElementaryAbelianSubgroup 2 D)
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : SectionEight.EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : SectionEight.EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16)
    (hv : IsCentralProductModel (VAt ctx.Γ ctx.criticalPath.firstStep) C4 Q8)
    (hi : IsModel (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a)
      (C2 × C4)) :
    IsModel (QAt ctx.Γ ctx.criticalPath.firstStep ⊓
      EAt ctx.Γ ctx.criticalPath.firstStep) Q8 := by
  exact eight_six_next_residual_intersection_model_of_small_v_local ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q T hprev hdefs hbase hindex data orders hnext hsmall hv hi

end Stellmacher.SectionEight
