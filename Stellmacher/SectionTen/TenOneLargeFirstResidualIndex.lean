module
public import Stellmacher.SectionTen.TenOneLargeChiefNoTransvection
public import Stellmacher.SectionTen.TenOneActorImageNontrivial
public import Stellmacher.SectionTen.TenOneGeneratedContainment
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Theory.GroupAction.FixedCoatomDisplacement
public import Mathlib.GroupTheory.IndexNormal

/-!
# The first-module residual-core index in source (15)

In the no-transvection case of the actual Section Ten configuration, the
intersection of the first module with the terminal residual two-core has
index two. The generated subgroup W lies in that same residual two-core.
The hypotheses are only the ambient Section Ten context, offset-two vertex,
and the standing absence of first-module transvections on the terminal
quotient. The chief factor remains an intrinsic quotient of O₂(E_terminal)
above V_terminal, with its supplied denominator, normality and action.

The cubic middle action puts O₂(E_terminal)∩Q_middle at index two in the
terminal residual core. If its commutator with V_first lay in V_terminal,
the selected actor would fix a coatom in the actual chief quotient. Its
nontriviality and the proved no-transvection theorem exclude the resulting
displacement of order at most two. Thus the commutator makes
V_first∩O₂(E_terminal) strictly larger than the common order-eight module
intersection. It is proper in the order-thirty-two first module, so Lagrange
forces order sixteen. This identifies the first seed with that intersection.
Finally, the residual core's actual punctured cubic action transports every
nonterminal conjugate seed back to the first one; terminal generators lie in
V_terminal. Hence the entire generated W lies in the residual core.

The public edge-index wrapper needs only the context and middle vertex,
without the no-transvection case, and is reused in (16)–(19).
The coatom-commutator escape is also exported unchanged for the actual
first-quotient four-divisibility argument in (19).

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.63,
equation (15), using the preceding chief-factor argument and (13)–(14).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem terminal_core_section_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    (QAt ctx.Γ middle).relIndex (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) = 2 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let Q := QAt ctx.Γ middle
  let edge := GAt ctx.Γ middle ⊓ P
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hUQend : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hQendP : QAt ctx.Γ ctx.criticalPath.a' ≤ P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hUedge : U ≤ edge := le_inf
    (hUQend.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2))
    (hUQend.trans hQendP)
  have hQP : Q ≤ GAt ctx.Γ middle := by
    change ctx.Γ.twoCoreAt middle ≤ GAt ctx.Γ middle
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQedge : Q ≤ edge := le_inf hQP
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2)
  have hcard : Nat.card edge = 2 * Nat.card Q :=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hterminal
  have hedge : Q.relIndex edge = 2 := by
    have hc := (Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQedge).toEquiv] at hc
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hc.trans hcard)
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle
      ⟨alignment,halignment⟩ (ctx.Γ.adjacent_symm hterminal)
  have hdiv : Q.relIndex U ∣ 2 := by
    let _ : (Q.subgroupOf edge).Normal := Subgroup.normal_of_index_eq_two hedge
    rw [←hedge,←Subgroup.relIndex_subgroupOf hUedge]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact (hescape (Subgroup.relIndex_eq_one.mp hone)).elim
  · exact htwo



private theorem first_index_of_commutator_escape
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hVcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 32)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hVU : VAt ctx.Γ ctx.criticalPath.a' ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
    (hnot : ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⊓ QAt ctx.Γ middle,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.a') :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let I := A ⊓ V
  let J := A ⊓ U
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hAcard : Nat.card A = 32 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    change Nat.card (v ctx.Γ ctx.criticalPath.firstStep) = 32
    rw [←hmove,v_act]
    exact (Nat.card_congr ((VAt ctx.Γ ctx.criticalPath.a').equivMapOfInjective
      (MulAut.conj (mover:G)⁻¹).toMonoidHom (MulAut.conj (mover:G)⁻¹).injective).toEquiv).symm.trans hVcard
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ Subgroup.normalizer (U:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hUQ : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hAP : A ≤ P := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hQA : QAt ctx.Γ middle ≤ Subgroup.normalizer (A:Set G) :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2).trans
      (stabilizer_le_normalizer_v ctx.Γ _)
  have hcommJ : ⁅U ⊓ QAt ctx.Γ middle,A⁆ ≤ J := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hQA))
    ((Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPU)))
  have hIJ : I ≤ J := inf_le_inf_left A hVU
  have hJlower : 8 < Nat.card J := by
    by_contra hn
    have heq : I=J := Subgroup.eq_of_le_of_card_ge hIJ (by rw [hIcard]; omega)
    exact hnot (hcommJ.trans (heq.symm.le.trans inf_le_right))
  have hJupper : Nat.card J < 32 := by
    by_contra hn
    have heq : J=A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard]; omega)
    exact (sectionTenOpeningData ctx middle hpath).first_noncontainment
      ((heq.symm.le.trans inf_le_right).trans hUQ)
  have hJdiv : Nat.card J ∣ 2^5 := by
    norm_num
    rw [←hAcard]
    exact Subgroup.card_dvd_of_le (show J≤A from inf_le_left)
  obtain ⟨power,hpower,hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hJdiv
  have hJcard : Nat.card J=16 := by
    interval_cases power <;> norm_num only [Nat.reducePow] at hcard <;> omega
  change Nat.card A = 2 * Nat.card J
  rw [hAcard,hJcard]


private theorem first_seed_le_residual_of_index_two
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' ≤
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') := by
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let J := A ⊓ U
  let K := A ⊓ QAt ctx.Γ ctx.criticalPath.a'
  have hUQ : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hJK : J ≤ K := inf_le_inf_left A hUQ
  have hJidx : J.relIndex A = 2 := by
    have hc := (J.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show J≤A from inf_le_left)).toEquiv] at hc
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hc.trans hindex)
  have hprod := Subgroup.relIndex_mul_relIndex J K A hJK inf_le_left
  rw [hJidx] at hprod
  have hKidx : K.relIndex A = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (dvd_of_mul_left_eq _ hprod) with hone | htwo
    · exact ((sectionTenOpeningData ctx middle hpath).first_noncontainment
        ((Subgroup.relIndex_eq_one.mp hone).trans inf_le_right)).elim
    · exact htwo
  have hJKidx : J.relIndex K = 1 := by rw [hKidx] at hprod; omega
  exact (Subgroup.relIndex_eq_one.mp hJKidx).trans inf_le_right

private theorem generated_le_terminal_residual_of_seed
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hVU : VAt ctx.Γ ctx.criticalPath.a' ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
    (hseed : VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' ≤
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) :
    conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle) ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') := by
  let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  obtain ⟨_,hfirst,hterminal,hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hUQ : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hQP : QAt ctx.Γ ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a' := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ GAt ctx.Γ ctx.criticalPath.a'
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hUedge : U ≤ GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a' := le_inf
    (hUQ.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2))
    (hUQ.trans hQP)
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle
      ⟨alignment,halignment⟩ (ctx.Γ.adjacent_symm hterminal)
  have htrans := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
    (sectionTenOpeningData ctx middle hpath).quotient_model).punctured_transitivity
      ctx.criticalPath.a' hterminal U hUedge hescape
  have hWQ : W ≤ QAt ctx.Γ ctx.criticalPath.a' :=
    (ten_one_generated_containment ctx middle hpath).trans (inf_le_left.trans
      (sInf_le ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩))
  rw [conjugateClosure,Subgroup.closure_le]
  rintro element ⟨mover,point,rfl⟩
  let x := (mover:G)*(point:G)*(mover:G)⁻¹
  let neighbor := ctx.Γ.act (mover:G)⁻¹ ctx.criticalPath.firstStep
  have hxV : x ∈ VAt ctx.Γ neighbor := by
    change x ∈ v ctx.Γ (ctx.Γ.act (mover:G)⁻¹ ctx.criticalPath.firstStep)
    rw [v_act,inv_inv]
    exact Subgroup.mem_map_of_mem _ point.property.1
  have hfix : ctx.Γ.act (mover:G)⁻¹ middle=middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp
      ((GAt ctx.Γ middle).inv_mem mover.property)
  have hneighbor := adjacent_act ctx.Γ (mover:G)⁻¹ hfirst
  rw [hfix] at hneighbor
  by_cases heq : neighbor=ctx.criticalPath.a'
  · apply hVU
    simpa only [heq] using hxV
  have hxQ : x ∈ QAt ctx.Γ ctx.criticalPath.a' :=
    hWQ (Subgroup.subset_closure ⟨mover,point,rfl⟩)
  obtain ⟨actor,hmove⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,hends⟩
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hneighbor,heq⟩
  change ctx.Γ.act (actor:G) ctx.criticalPath.firstStep = neighbor at hmove
  have hbackV : (actor:G)*x*(actor:G)⁻¹ ∈ VAt ctx.Γ ctx.criticalPath.firstStep := by
    change x ∈ v ctx.Γ neighbor at hxV
    rw [←hmove,v_act,Subgroup.mem_map_equiv] at hxV
    simpa only [MulAut.conj_symm_apply,inv_inv] using hxV
  have hbackQ : (actor:G)*x*(actor:G)⁻¹ ∈ QAt ctx.Γ ctx.criticalPath.a' :=
    (QAt ctx.Γ ctx.criticalPath.a').mul_mem
      ((QAt ctx.Γ ctx.criticalPath.a').mul_mem (hUQ actor.property) hxQ)
      ((QAt ctx.Γ ctx.criticalPath.a').inv_mem (hUQ actor.property))
  have hbackU := hseed ⟨hbackV,hbackQ⟩
  have hx := U.mul_mem (U.mul_mem (U.inv_mem actor.property) hbackU) actor.property
  change x ∈ U
  simpa only [mul_assoc,inv_mul_cancel,inv_mul_cancel_left,one_mul,mul_one] using hx

private theorem terminal_core_commutator_escape
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ∧
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⊓ QAt ctx.Γ middle,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.a'
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  obtain ⟨element,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hcard,hselected⟩ := hcases.resolve_left (hno element hactor hout)
  let actor : P := ⟨element,
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor⟩
  obtain ⟨hPU,D,hVD,hDU,hPD,hDnormal,chief,hformulaChief,hWc,hne,hirr,hfull,hres,hnotwo⟩ :=
    ten_one_large_nontransvection_chief_factor ctx middle hpath actor hactor action hformula
      hkernel hout hcard hselected hno
  let _ := hDnormal
  let _ := hWc
  let _ := hne
  refine ⟨hVD.trans hDU.le,?_⟩
  intro hcomm
  have hnontrivial : chief actor ≠ 1 :=
    ten_one_first_actor_image_ne_one ctx middle hpath actor hactor hout chief hres
  have hnotone : Nat.card (commutatorAction (Subgroup.zpowers (chief actor))
      (U ⧸ D.subgroupOf U)) ≠ 1 := by
    intro hone
    have htriv := actsTrivially_of_commutatorAction_eq_bot (Subgroup.card_eq_one.mp hone)
    apply hnontrivial
    ext point
    exact htriv ⟨chief actor,Subgroup.mem_zpowers _⟩ point
  have hKindex : (U ⊓ QAt ctx.Γ middle).relIndex U ∣ 2 := by
    rw [Subgroup.inf_relIndex_left,terminal_core_section_index ctx middle hpath]
  have hKcomm : ⁅U ⊓ QAt ctx.Γ middle,Subgroup.zpowers (actor:G)⁆ ≤ D :=
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hcomm).trans hVD
  have hrel := Subgroup.quotient_commutator_card_le_two_of_fixed_coatom
    P U D (U ⊓ QAt ctx.Γ middle) hDU.le hPU hDnormal hWc chief hformulaChief
      actor inf_le_left hKindex hKcomm
  have hDP : Subgroup.zpowers (actor:G) ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hinternal : (Subgroup.zpowers (actor:G)).subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hCU : ⁅U,Subgroup.zpowers (actor:G)⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPU)
  have heq := Subgroup.relIndex_sup_right
    (⁅U,Subgroup.zpowers (actor:G)⁆.subgroupOf U) (D.subgroupOf U)
  rw [←Subgroup.subgroupOf_sup hCU hDU.le,
    Subgroup.relIndex_subgroupOf (sup_le hCU hDU.le),Subgroup.relIndex_subgroupOf hCU] at heq
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card
    P U D (Subgroup.zpowers (actor:G)) hPU hDP hDnormal chief hformulaChief
  rw [hinternal,MonoidHom.map_zpowers,←heq] at hrank
  have hbound := hrank.trans_le hrel
  let displacement := commutatorAction (Subgroup.zpowers (chief actor)) (U ⧸ D.subgroupOf U)
  have hbound' : Nat.card displacement ≤ 2 := hbound
  have hnotone' : Nat.card displacement ≠ 1 := hnotone
  have hnotwo' : Nat.card displacement ≠ 2 := hnotwo
  have hpos' : 0 < Nat.card displacement := Nat.card_pos
  omega

public theorem ten_one_large_first_residual_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2 ∧
    conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle) ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') := by
  obtain ⟨_,hVcard,hIcard⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  obtain ⟨hVU,hnot⟩ := terminal_core_commutator_escape ctx middle hpath hno
  have hindex := first_index_of_commutator_escape ctx middle hpath hVcard hIcard hVU hnot
  exact ⟨hindex,generated_le_terminal_residual_of_seed ctx middle hpath hVU
    (first_seed_le_residual_of_index_two ctx middle hpath hindex)⟩


/-- The terminal residual core crosses the middle core in index two, as in (7.6)(b). -/
public theorem ten_one_terminal_residual_middle_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    (QAt ctx.Γ middle).relIndex (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) = 2 :=
  terminal_core_section_index ctx middle hpath

/-- The terminal core is above the module, and its middle coatom has
noncentral first-module commutator, as used in (15) and (19). -/
public theorem ten_one_large_terminal_core_commutator_escape
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    VAt ctx.Γ ctx.criticalPath.a' ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ∧
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⊓ QAt ctx.Γ middle,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.a' :=
  terminal_core_commutator_escape ctx middle hpath hno

end Stellmacher.SectionTen
