module
public import Stellmacher.SectionNine.NineTenTwoStepClassification
public import Stellmacher.SectionNine.NineEightWTransfer
public import Stellmacher.SectionNine.NineSevenNeighborJoinBounds
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionOne.CoreKernelInvolutionInvariantFour
public import Stellmacher.SectionOne.OneSevenLargeTwoGroupFixedSupport
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The good neighbor's neighborhood centralizes the third module

At critical length five, retain the terminal order-thirty-two module, its
wreath core quotient, and the order-eight backward intersection. Suppose a
selected neighbor lambda of the first vertex has the universal triple
intersection from (9.10)(**). Its actual neighborhood join centralizes the
third module and lies in the terminal stabilizer. No generating-family
condition or desired commutator bound is added to these hypotheses.

The source's commutativity step uses the actual four-plane in Vthird/Zthird.
The second-core image has order eight and preserves this plane; each Vrho
involution fixes it. Rank-nullity and the canonical support calculation put
its displacement in that plane. Lift to the actual module intersection, then
use mutual normalization and the triple intersection to put the ambient
commutator in Zfirst. This line is disjoint from Zthird and fixed by the whole
second core. A nonzero line would lie in a canonical support and its disjoint
conjugate, which is impossible. One two-arc conjugator transfers the entire
terminal calculation, including both modules, core, and center line together.

Joining the rho centralizations gives the first conclusion. The distance
bound places the neighborhood in the preterminal stabilizer, and its
centralization of the penultimate center lets the proved residual/stabilizer
transfer give terminal containment. Source: Stellmacher, Journal of Algebra
190 (1997), printed p.58, paragraph from (**) to (9).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

set_option maxHeartbeats 1400000 in
private theorem terminal_good_subgroup_commutes
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a')=2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G)=2^3)
    (K : Subgroup G) [IsElementaryAbelian 2 K]
    (hKcore : K≤QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hUK : VAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (K:Set G))
    (hKI : K≤Subgroup.centralizer ((VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G):Set G))
    (htriple : K ⊓ (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) ≤ ZAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    ⁅VAt ctx.Γ ctx.criticalPath.a',K⁆=⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let previous := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let middle := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let I := U⊓VAt Γ previous
  have hshort : 1<cp.length := by change 3<cp.length at hb; omega
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) previous :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  have hleft := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort previous hpath)
  have hright := nine_five_penultimate_adjacent ctx.toLocalContext
  obtain ⟨align,hmiddle,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨align,hterminal⟩
  have hprevOrbit := nine_five_penultimate_neighbor_orbit ctx.toLocalContext previous hleft
  have hdata := nine_next_center_commutator_and_kernel ctx hshort cp.a' horbit
  have hZcard : Nat.card Z=2 := hdata.1
  have hprevCard : Nat.card (ZAt Γ previous)=2 :=
    (nine_next_center_commutator_and_kernel ctx hshort previous hprevOrbit).1
  have hgeom := nine_nine_terminal_intersection_core_normalized ctx hshort
  have hcenters := (nine_seven_center_join ctx middle ⟨align,hmiddle⟩).2
  have hZmiddle : Z≤ZAt Γ middle :=
    (hcenters cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hright)).2
  have hZprev : ZAt Γ previous≤ZAt Γ middle :=
    (hcenters previous ((mem_neighborhood_iff_adjacent Γ).mpr hleft)).2
  have hZI : Z≤I := hZmiddle.trans hgeom.1
  have hZU : Z≤U := hZI.trans inf_le_left
  have hdisj : Disjoint (ZAt Γ previous) Z :=
    (nine_three_center_split ctx hshort ⟨align,hmiddle⟩ hleft hright
      (nine_five_previous_ne_terminal ctx.toLocalContext hshort previous hpath)).2.1
  have hQP : QAt Γ middle≤P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hright) default).2.2
  have hQself : QAt Γ middle≤GAt Γ middle := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hKP : K≤P := hKcore.trans hQP
  have hPU : P≤Subgroup.normalizer (U:Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hsolv : Group.IsSolvable P := stabilizer_solvable_of_neighbor ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hright))
  obtain ⟨hN,hW,action,hact,hkernel⟩ := nine_next_quotient_conjugation_action ctx hshort cp.a' horbit
  let _ := hN
  let _ := hW
  let W := U⧸Z.subgroupOf U
  let q : U→*W := QuotientGroup.mk' (Z.subgroupOf U)
  let J := (I.subgroupOf U).map q
  let Sbar := ((QAt Γ middle).subgroupOf P).map action.rangeRestrict
  have hSbarCard : Nat.card Sbar=8 := by
    apply nine_nine_terminal_core_image_card_eight ctx hshort action.rangeRestrict
      action.rangeRestrict_surjective
    · rw [MonoidHom.ker_rangeRestrict,hkernel]
    · exact hmodel
  have hSbarTwo : IsPGroup 2 Sbar :=
    IsPGroup.of_card (p:=2) (n:=3) (by simpa using hSbarCard)
  have hWcard : Nat.card W=16 := by
    have hh := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hcard] at hh
    change Nat.card W*2=2^5 at hh
    omega
  have hJcard : Nat.card J=4 := by
    have hh := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hinter] at hh
    change Z.relIndex I*2=2^3 at hh
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf (show I≤U from inf_le_left)] at hrel
    change Z.relIndex I=Nat.card J at hrel
    omega
  have hJInv : ∀ s:Sbar, ∀ w∈J, (s:action.range).val w∈J := by
    rintro s w ⟨v,hv,rfl⟩
    obtain ⟨mover,hmover,heq⟩ := s.property
    rw [←heq]
    change action mover (q v)∈J
    rw [hact]
    exact Subgroup.mem_map_of_mem q
      ((Subgroup.mem_normalizer_iff.mp (hgeom.2.2 (hQself hmover)) (v:G)).mp hv)
  have hcyclic (actor:P) : (Subgroup.zpowers (actor:G)).subgroupOf P=Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr actor.property),MonoidHom.map_zpowers]
    rfl
  have hcyclicBot : ∀ actor:P, (actor:G)∈K → ⁅U,Subgroup.zpowers (actor:G)⁆=⊥ := by
    intro actor hactor
    let R := ⁅U,Subgroup.zpowers (actor:G)⁆
    have hRU : R≤U := Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr actor.property).trans hPU)
    have hRK : R≤K :=
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hUK)
    have hlineImage := Subgroup.quotient_conjugation_commutatorAction_eq_image
      P U Z (Subgroup.zpowers (actor:G)) hPU (Subgroup.zpowers_le.mpr actor.property) hN action hact
    rw [hcyclic,MonoidHom.map_zpowers] at hlineImage
    have hfix : ∀ w∈J, action actor w=w := by
      rintro w ⟨v,hv,rfl⟩
      rw [hact]
      congr 1
      apply Subtype.ext
      change (actor:G)*(v:G)*(actor:G)⁻¹=(v:G)
      have hc := Subgroup.mem_centralizer_iff.mp (hKI hactor) (v:G) hv
      rw [←hc,mul_inv_cancel_right]
    have hsquare : (action actor)^2=1 := by
      rw [←map_pow]
      have ht : actor^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (actor:G) hactor)
      rw [ht,map_one]
    have hlineJ := SectionOne.core_kernel_involution_displacement_le_invariant_four
      hsolv action hkernel hWcard Sbar hSbarTwo (by rw [hSbarCard]; decide)
        J hJcard hJInv actor hsquare hfix
    rw [hlineImage] at hlineJ
    have hRI : R≤I := by
      intro r hr
      have hmem : (⟨r,hRU hr⟩:U)∈((I.subgroupOf U).map q).comap q :=
        hlineJ (Subgroup.mem_map_of_mem q hr)
      rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
        (Subgroup.subgroupOf_mono U hZI)] at hmem
      exact hmem
    have hRline : R≤ZAt Γ previous := (le_inf hRK hRI).trans htriple
    by_contra hRne
    have hRlower := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    have hRupper := Subgroup.card_le_of_le hRline
    have hRcard : Nat.card R=2 := by omega
    have hRZ : Z⊓R=⊥ := le_bot_iff.mp
      ((le_inf (inf_le_right.trans hRline) inf_le_left).trans hdisj.le_bot)
    have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action actor)) W)=2 := by
      have hh := Subgroup.quotient_conjugation_commutatorAction_card P U Z
        (Subgroup.zpowers (actor:G)) hPU (Subgroup.zpowers_le.mpr actor.property) hN action hact
      rw [hcyclic,MonoidHom.map_zpowers,←Subgroup.inf_relIndex_right Z R,hRZ] at hh
      simpa [Subgroup.relIndex,hRcard] using hh
    obtain ⟨hyp,hD⟩ := SectionOne.core_kernel_transvection_factor hsolv action hkernel actor hrank
    let D := ⁅SectionOne.oddCore action.range,Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict actor)
    let line := commutatorAction (Subgroup.zpowers (action actor)) W
    have hlineD : line≤commutatorAction D W := by
      have hlin : commutatorAction (Subgroup.zpowers (action.rangeRestrict actor)) W=line := by
        rw [←commutatorAction_map_actor_subtype action.range,MonoidHom.map_zpowers]
        rfl
      rw [←hlin]
      rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
      apply Subgroup.closure_mono
      rintro w ⟨mover,v,rfl⟩
      exact ⟨⟨mover,Subgroup.mem_sup_right mover.property⟩,v,rfl⟩
    have hlineFix : line≤FixedPoints.subgroup Sbar W := by
      intro w hw s
      change w∈commutatorAction (Subgroup.zpowers (action actor)) W at hw
      rw [hlineImage] at hw
      obtain ⟨v,hv,rfl⟩ := hw
      obtain ⟨mover,hmover,heq⟩ := s.property
      have hz := hZprev (hRline hv)
      have homega := (lemma_seven_three ctx.sectionSeven Γ).center_core middle cp.a'
        ((mem_neighborhood_iff_adjacent Γ).mpr hright) hz
      have hc := ((mem_omegaOneCenterAmbient_iff (QAt Γ middle) (v:G)).mp homega).2.2
        (mover:G) hmover
      change ((s:action.range):MulAut W) (q v)=q v
      rw [←heq]
      change action mover (q v)=q v
      rw [hact]
      congr 1
      apply Subtype.ext
      change (mover:G)*(v:G)*(mover:G)⁻¹=(v:G)
      rw [hc,mul_inv_cancel_right]
    have hbot : line=⊥ := le_bot_iff.mp ((le_inf hlineD hlineFix).trans_eq
      (SectionOne.oneSevenFactor_large_two_group_support_fixed_eq_bot hyp D Sbar hD
        hSbarTwo hWcard (by rw [hSbarCard]; decide)))
    change Nat.card line=2 at hrank
    rw [hbot,Subgroup.card_bot] at hrank
    omega
  apply le_bot_iff.mp
  apply Subgroup.commutator_le.mpr
  intro u hu k hk
  exact hcyclicBot ⟨k,hKP hk⟩ hk ▸
    Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers k)

set_option maxHeartbeats 1800000 in
public theorem nine_ten_good_neighbor_neighborhood_support
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a')=2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G)=2^3)
    (lambda : ctx.Γ.Vertex) (hlambda : lambda∈Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (htriple : ∀ rho, rho∈Neighborhood ctx.Γ lambda → rho≠ctx.criticalPath.firstStep →
      VAt ctx.Γ rho ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        VAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩)=ZAt ctx.Γ ctx.criticalPath.firstStep) :
    let third := ctx.criticalPath.path ⟨3,by omega⟩
    GeneratedNeighborhoodV ctx.Γ lambda ≤ Subgroup.centralizer (VAt ctx.Γ third:Set G) ∧
      GeneratedNeighborhoodV ctx.Γ lambda ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=5 := hb
  have hshort : 1<cp.length := by omega
  have hlong : 4<cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let previous := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let middle := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hthirdPrev : third=previous := by apply congrArg cp.path; apply Fin.ext; dsimp; omega
  have hfirstSecond : Γ.adjacent cp.firstStep second := by
    have hh := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hh
    rwa [cp.path_first] at hh
  have hsecondThird : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hfirstThird : cp.firstStep≠third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  have hfirstLambda : Γ.adjacent cp.firstStep lambda :=
    (mem_neighborhood_iff_adjacent Γ).mp hlambda
  have hfirstIn : cp.firstStep∈Neighborhood Γ lambda :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstLambda)
  obtain ⟨target,htarget⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirstSecond)
  have hsecondOrbit : IsConjugateVertex Γ cp.a second := ⟨target,htarget⟩
  obtain ⟨align,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  change Γ.act align cp.a=middle at halign
  have hmiddleOrbit : IsConjugateVertex Γ middle second := by
    refine ⟨align⁻¹*(target:G),?_⟩
    have hinv : Γ.act align⁻¹ middle=cp.a := by
      rw [←halign,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
    rw [Γ.act_mul,hinv]
    exact htarget
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreviousAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort previous
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  obtain ⟨mover,hmoveThird,hmoveSecond,hmoveFirst⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven Γ hterminalAdj hpreviousAdj
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort previous
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
    hsecondThird (Γ.adjacent_symm hfirstSecond) hfirstThird.symm hmiddleOrbit
    (lemma_nine_three_ambient ctx hshort second hsecondOrbit).1
  let e := MulAut.conj mover
  have hVthird : (VAt Γ third).map e.toMonoidHom=VAt Γ cp.a' := by
    rw [←hmoveThird]
    change (v Γ (Γ.act mover cp.a')).map e.toMonoidHom=v Γ cp.a'
    rw [v_act]
    exact Subgroup.conjBy_inv' _ _
  have hVfirst : (VAt Γ cp.firstStep).map e.toMonoidHom=VAt Γ previous := by
    rw [←hmoveFirst]
    change (v Γ (Γ.act mover previous)).map e.toMonoidHom=v Γ previous
    rw [v_act]
    exact Subgroup.conjBy_inv' _ _
  have hZfirst : (ZAt Γ cp.firstStep).map e.toMonoidHom=ZAt Γ previous := by
    rw [←hmoveFirst]
    change (z Γ (Γ.act mover previous)).map e.toMonoidHom=z Γ previous
    rw [z_act]
    exact Subgroup.conjBy_inv' _ _
  have hQsecond : (QAt Γ second).map e.toMonoidHom=QAt Γ middle := by
    rw [←hmoveSecond]
    change (q Γ (Γ.act mover middle)).map e.toMonoidHom=q Γ middle
    rw [q_act]
    exact Subgroup.conjBy_inv' _ _
  have hdistance : Γ.distance lambda second≤2 := by
    have hh := Γ.distance_le_of_path 2 ![lambda,cp.firstStep,second] (by
      intro i
      fin_cases i
      · exact Γ.adjacent_symm hfirstLambda
      · exact hfirstSecond)
    exact hh
  have hWQ : GeneratedNeighborhoodV Γ lambda≤QAt Γ second :=
    nine_seven_neighborhood_le_core_of_distance Γ cp lambda second (by omega)
  have hWsecondQlambda : GeneratedNeighborhoodV Γ second≤QAt Γ lambda := by
    apply nine_seven_neighborhood_le_core_of_distance Γ cp second lambda
    rw [Γ.distance_symm]
    omega
  have hVthirdQlambda : VAt Γ third≤QAt Γ lambda :=
    (nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr hsecondThird)).trans hWsecondQlambda
  have hWabel := nine_eight_neighborhood_abelian ctx.toLocalContext hlong lambda
  have hWfirst : GeneratedNeighborhoodV Γ lambda≤Subgroup.centralizer (VAt Γ cp.firstStep:Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWabel).trans
      (Subgroup.centralizer_le (nine_eight_v_le_generated_neighborhood Γ hfirstIn))
  have hcomm : GeneratedNeighborhoodV Γ lambda≤Subgroup.centralizer (VAt Γ third:Set G) := by
    apply sSup_le
    rintro subgroup ⟨rho,hrho,rfl⟩
    by_cases heq : rho=cp.firstStep
    · subst rho
      have hh := nine_five_previous_module_commutes_first ctx.toLocalContext hshort previous
        ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
      rw [←hthirdPrev,Subgroup.commutator_comm] at hh
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh
    have hrhoW : VAt Γ rho≤GeneratedNeighborhoodV Γ lambda :=
      nine_eight_v_le_generated_neighborhood Γ hrho
    have hthirdGrho : VAt Γ third≤GAt Γ rho := hVthirdQlambda.trans
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core lambda rho hrho default).2.2
    have hnorm : VAt Γ third≤Subgroup.normalizer (VAt Γ rho:Set G) :=
      hthirdGrho.trans (stabilizer_le_normalizer_v Γ rho)
    have hfixed : VAt Γ rho≤Subgroup.centralizer
        ((VAt Γ third⊓VAt Γ cp.firstStep:Subgroup G):Set G) :=
      (hrhoW.trans hWfirst).trans (Subgroup.centralizer_le inf_le_right)
    have helem : IsElementaryAbelian 2 (VAt Γ rho) := by
      obtain ⟨g,hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity lambda hfirstIn hrho
      let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
      rw [←hg]
      change IsElementaryAbelian 2 (v Γ (Γ.act (g:G) cp.firstStep))
      rw [v_act]
      exact IsElementaryAbelian.map (MulAut.conj (g:G)⁻¹).toMonoidHom
    let _ := helem
    let K := (VAt Γ rho).map e.toMonoidHom
    let _ : IsElementaryAbelian 2 K := IsElementaryAbelian.map e.toMonoidHom
    have hKcore : K≤QAt Γ middle := by
      rw [←hQsecond]
      exact Subgroup.map_mono (hrhoW.trans hWQ)
    have hUK : VAt Γ cp.a'≤Subgroup.normalizer (K:Set G) := by
      rw [←hVthird]
      exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map e.toMonoidHom)
    have hKI : K≤Subgroup.centralizer
        ((VAt Γ cp.a'⊓VAt Γ previous:Subgroup G):Set G) := by
      have hh := (Subgroup.map_mono (f:=e.toMonoidHom) hfixed).trans
        (Subgroup.map_centralizer_le_centralizer_image _ e.toMonoidHom)
      change K≤Subgroup.centralizer (((VAt Γ third⊓VAt Γ cp.firstStep).map e.toMonoidHom):Set G) at hh
      rw [Subgroup.map_inf _ _ _ e.injective,hVthird,hVfirst] at hh
      exact hh
    have htriple' : K⊓(VAt Γ cp.a'⊓VAt Γ previous)≤ZAt Γ previous := by
      rw [←hVthird,←hVfirst,←Subgroup.map_inf _ _ _ e.injective,
        ←Subgroup.map_inf _ _ _ e.injective,←hZfirst]
      apply Subgroup.map_mono
      have hh := htriple rho hrho heq
      change VAt Γ rho⊓VAt Γ cp.firstStep⊓VAt Γ third=ZAt Γ cp.firstStep at hh
      simpa only [inf_assoc,inf_comm,inf_left_comm] using hh.le
    have hbot := terminal_good_subgroup_commutes ctx (by omega) hcard hmodel hinter
      K hKcore hUK hKI htriple'
    have hactual : ⁅VAt Γ third,VAt Γ rho⁆=⊥ := by
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      rw [Subgroup.map_commutator,hVthird,Subgroup.map_bot]
      exact hbot
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hactual)
  refine ⟨hcomm,?_⟩
  have hWprev : GeneratedNeighborhoodV Γ lambda≤GAt Γ previous :=
    nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong lambda hlambda
  have hZmiddleV : ZAt Γ middle≤VAt Γ third := by
    rw [hthirdPrev]
    exact nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hpreviousAdj)
  have hcentral : GeneratedNeighborhoodV Γ lambda≤Subgroup.centralizer (ZAt Γ middle:Set G) :=
    hcomm.trans (Subgroup.centralizer_le hZmiddleV)
  exact nine_eight_stabilizer_transfer_of_commutator ctx.sectionSeven Γ middle previous cp.a'
    ((mem_neighborhood_iff_adjacent Γ).mpr hpreviousAdj)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) _ hWprev
    ((Subgroup.commutator_mono hcentral le_rfl).trans
      (nine_eight_penultimate_centralizer_commutator ctx))


end Stellmacher.SectionNine
