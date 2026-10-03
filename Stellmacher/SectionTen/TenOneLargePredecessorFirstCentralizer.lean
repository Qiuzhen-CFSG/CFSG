module
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Stellmacher.SectionTen.TenOneLargeCentralLayerContainment
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionTen.TenOneLargeFirstCoreContainment
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Theory.GroupTheory.FrobeniusReflectionResidualTransfer
public import Stellmacher.SectionTen.TenOneLargeCoreDerivedContainment

/-!
# The predecessor intersection centralizes the first module

Let previous be a neighbor of the initial vertex, distinct from firstStep,
and assume its center escapes the terminal core. In the actual large branch,
the intersection of Q_previous with the terminal module centralizer inside
Q_terminal centralizes V_first. The original context and no-transvection
hypothesis are retained; the opposite center escape is not needed here.

An actual residual two-arc transport fixes firstStep and carries the terminal
module to the previous module. Their images in the first core quotient both
have order two. If the images were equal, the previous center would have
terminal displacement in Z_first, forcing a forbidden quotient transvection.
Thus the two images are distinct reflections in the proved Frobenius20 model.

The actual intersection C2 centralizes V_terminal and commutes with V_previous
modulo V_first. The independent core-derived bound Q_first'≤V_first and the
finite two-reflection transfer give C2≤Q_first and [C2,E_first]≤V_first.
The natural center commutator bound and three-subgroups, with the transported
full residual support [V_first,E_first]=V_first, then give [C2,V_first]=1.

Source: Stellmacher (10.1), Journal of Algebra190 (1997), printed p.65,
the first implications in the final predecessor paragraph. The two-reflection
argument proves the printed residual transfer explicitly; no extra local
faithfulness, source20 commutator, or final core-index conclusion is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u v
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem cross_center_commutator_impossible
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (actor:G) (ha:actor∈VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout:actor∉QAt ctx.Γ ctx.criticalPath.a')
    (hcomm:⁅VAt ctx.Γ ctx.criticalPath.a',zpowers actor⁆≤ZAt ctx.Γ ctx.criticalPath.firstStep) : False := by
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let Zf:=ZAt ctx.Γ ctx.criticalPath.firstStep
  let D:=⁅V,zpowers actor⁆
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hd:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  have hf:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  have hDne : D≠⊥:=by
    intro heq
    apply hout
    apply (hd.2.2 actor ((lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 ha)).mp
    change D≤Z
    rw [heq]
    exact bot_le
  have hDcard : 2≤Nat.card D:=by
    have hh:1<Nat.card D:=(Subgroup.one_lt_card_iff_ne_bot D).mpr hDne
    omega
  have hD : D=Zf:=Subgroup.eq_of_le_of_card_ge hcomm (by rw [hf.1];exact hDcard)
  apply hno actor ha hout
  change Nat.card (D⊔Z:Subgroup G)=2*Nat.card Z
  rw [hD,←(sectionTenOpeningData ctx middle hpath).center_direct_product.1,
    (sectionTenOpeningData ctx middle hpath).center_card,hd.1]


private theorem predecessor_image_pair
    {X : Type v} [Group X]
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous:ctx.Γ.Vertex) (hadj:ctx.Γ.adjacent ctx.criticalPath.a previous)
    (hne:previous≠ctx.criticalPath.firstStep)
    (hreverse:¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a')
    (mover:G) (hfix:ctx.Γ.act mover ctx.criticalPath.firstStep=ctx.criticalPath.firstStep)
    (hmove:ctx.Γ.act mover ctx.criticalPath.a'=previous)
    (f:GAt ctx.Γ ctx.criticalPath.firstStep→*X)
    (hker:f.ker=(QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    let P:=GAt ctx.Γ ctx.criticalPath.firstStep
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let Vp:=VAt ctx.Γ previous
    V≤P ∧ Vp≤P ∧ ZAt ctx.Γ previous≤VAt ctx.Γ ctx.criticalPath.firstStep ∧
    Nat.card ((V.subgroupOf P).map f)=2 ∧ Nat.card ((Vp.subgroupOf P).map f)=2 ∧
    ((V.subgroupOf P).map f)≠((Vp.subgroupOf P).map f) := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let R:=QAt ctx.Γ ctx.criticalPath.firstStep
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Vp:=VAt ctx.Γ previous
  let Zp:=ZAt ctx.Γ previous
  let Zf:=ZAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hRP:R≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVP:V≤P:=(show V≤GeneratedNeighborhoodV ctx.Γ middle from le_sSup
    ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩).trans
      ((nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle).trans
        (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
          ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2))
  let aut:=MulAut.conj mover⁻¹
  have hPmap:P.map aut.toMonoidHom=P:=by
    change conjugateBy (stabilizer ctx.Γ ctx.criticalPath.firstStep) mover⁻¹=_
    rw [←stabilizer_act,hfix]
  have hRmap:R.map aut.toMonoidHom=R:=by
    change (q ctx.Γ ctx.criticalPath.firstStep).map _=q ctx.Γ ctx.criticalPath.firstStep
    rw [←q_act,hfix]
  have hVmap:V.map aut.toMonoidHom=Vp:=by
    change (v ctx.Γ ctx.criticalPath.a').map _=v ctx.Γ previous
    rw [←v_act,hmove]
  have hVpP:Vp≤P:=hVmap.symm.le.trans ((map_mono hVP).trans_eq hPmap)
  have hidx:R.relIndex V=2:=ten_one_large_terminal_first_core_relIndex ctx middle hpath hno
  have hidxp:R.relIndex Vp=2:=by
    rw [←hVmap,←hRmap,relIndex_map_map_of_injective _ _ aut.injective]
    exact hidx
  have hc:Nat.card ((V.subgroupOf P).map f)=2:=by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hVP]
    exact hidx
  have hcp:Nat.card ((Vp.subgroupOf P).map f)=2:=by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hVpP]
    exact hidxp
  have hsplit:=nine_three_center_split ctx.toAmbientSectionNineContext hshort
    (middle:=ctx.criticalPath.a) ⟨1,ctx.Γ.act_one _⟩ hadj ctx.criticalPath.firstStep_adj hne
  have hZpA:Zp≤A:=(show Zp≤ZAt ctx.Γ ctx.criticalPath.a by rw [hsplit.1];exact le_sup_left).trans
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  obtain ⟨align,halign⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity ctx.criticalPath.a
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hVpC:Vp≤centralizer (Zp:Set G):=
    (show Vp≤GAt ctx.Γ previous from (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort previous).trans (by
      change ctx.Γ.twoCoreAt previous≤ctx.Γ.stabilizer previous
      rw [ctx.Γ.twoCoreAt_def];exact twoCoreIn_le _)).trans
      (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext previous ⟨align,halign⟩)
  refine ⟨hVP,hVpP,hZpA,hc,hcp,?_⟩
  intro heq
  have hVjoin:V≤Vp⊔R:=by
    intro v hv
    have hh:f ⟨v,hVP hv⟩∈(Vp.subgroupOf P).map f:=heq ▸ mem_map_of_mem f hv
    obtain ⟨w,hw,hwv⟩:=hh
    have hratio : v/(w:G)∈R:=by
      have hr:f (⟨v,hVP hv⟩/w)=1:=by
        rw [map_div]
        exact div_eq_one.mpr hwv.symm
      have hm:=MonoidHom.mem_ker.mpr hr
      rw [hker] at hm
      exact hm
    have hh:=(Vp⊔R).mul_mem (mem_sup_right hratio) (mem_sup_left hw)
    change (v/(w:G))*(w:G)∈Vp⊔R at hh
    simpa only [div_mul_cancel] using hh
  have hRZp:⁅R,Zp⁆≤Zf:=by
    rw [commutator_comm]
    exact (commutator_mono hZpA le_rfl).trans_eq
      (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
        ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩).2.1
  have hVpZp:⁅Vp,Zp⁆≤Zf:=by
    rw [commutator_eq_bot_iff_le_centralizer.mpr hVpC]
    exact bot_le
  have hVpre:V≤commutatorPreimage P Zp Zf:=hVjoin.trans (sup_le
    (le_commutatorPreimage hVpP hVpZp) (le_commutatorPreimage hRP hRZp))
  have hVZp:⁅V,Zp⁆≤Zf:=(commutator_mono hVpre le_rfl).trans
    (commutator_commutatorPreimage_le P Zp Zf (stabilizer_le_normalizer_z ctx.Γ _))
  obtain ⟨actor,ha,hout⟩:=SetLike.not_le_iff_exists.mp hreverse
  exact cross_center_commutator_impossible ctx middle hpath hno actor (hZpA ha) hout
    ((commutator_mono le_rfl (zpowers_le.mpr ha)).trans hVZp)

private theorem predecessor_first_residual_bound
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous:ctx.Γ.Vertex) (hadj:ctx.Γ.adjacent ctx.criticalPath.a previous)
    (hne:previous≠ctx.criticalPath.firstStep)
    (hreverse:¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a') :
    let C:=(QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G))⊓QAt ctx.Γ previous
    C≤QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C,EAt ctx.Γ ctx.criticalPath.firstStep⁆≤VAt ctx.Γ ctx.criticalPath.firstStep := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let Q:=QAt ctx.Γ ctx.criticalPath.firstStep
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Vp:=VAt ctx.Γ previous
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let C1:=QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (V:Set G)
  let C:=C1⊓QAt ctx.Γ previous
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hmodels (vertex:ctx.Γ.Vertex) (hv:IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex) :
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two:=
    (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hshort vertex hv).1
  obtain ⟨_,hfirst,hterminal,hends⟩:=sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmover,_,hmove⟩:=nine_seven_residual_two_arc_transport_of_opposite_models
    ctx.toLocalContext.toSectionNineLocalContext hmodels ctx.criticalPath.firstStep
    ⟨1,ctx.Γ.act_one _⟩ middle ctx.criticalPath.a' ctx.criticalPath.a previous
    (ctx.Γ.adjacent_symm hfirst) hterminal hends
    (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj) hadj hne.symm
  have hEdef:E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP:E≤P:=hEdef ▸ twoResidualIn_le P
  have hfix:ctx.Γ.act mover ctx.criticalPath.firstStep=ctx.criticalPath.firstStep:=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def ctx.criticalPath.firstStep) _).mp (hEP hmover)
  obtain ⟨φ,_hfaith,f,_hsurj,hker⟩:=ten_one_large_first_frobenius ctx middle hpath hno
  obtain ⟨hVP,hVpP,hZpA,hVcard,hVpcard,himages⟩:=
    predecessor_image_pair ctx middle hpath hno previous hadj hne hreverse mover hfix hmove f hker
  have hQP:Q≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hAQ:A≤Q:=neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _
  have hAP:A≤P:=hAQ.trans hQP
  have hCjoin:C≤V⊔Q:=inf_le_left.trans (ten_one_large_first_core_containment ctx middle hpath hno)
  have hCP:C≤P:=hCjoin.trans (sup_le hVP hQP)
  have hPA:P≤normalizer (A:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  let _ : (A.subgroupOf P).Normal:=(normal_subgroupOf_iff_le_normalizer hAP).mpr hPA
  have hCV:⁅C,V⁆=⊥:=commutator_eq_bot_iff_le_centralizer.mpr (inf_le_left.trans inf_le_right)
  obtain ⟨align,halign⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity ctx.criticalPath.a
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hCVp:⁅C,Vp⁆≤A:=by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl (show C≤QAt ctx.Γ previous from inf_le_right)).trans_eq
      (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort previous ⟨align,halign⟩).2.1).trans hZpA
  have hQQ:⁅Q,Q⁆≤A:=by
    rw [←show DerivedAmbient Q=⁅Q,Q⁆ from map_subtype_commutator Q]
    exact ten_one_large_first_core_derived_le_module ctx middle hpath hno
  have hEnative:E.subgroupOf P=twoResidualSubgroup P:=by
    rw [hEdef,twoResidualIn,twoResidualAmbient]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hEkill:E.subgroupOf P≤(SemidirectProduct.rightHom.comp f).ker:=by
    rw [hEnative,SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact SectionThree.hktPResidual_le_ker_of_isPGroup _
      (IsPGroup.of_card (p:=2) (n:=2) (by norm_num [C4]))
  have hEimage:(E.subgroupOf P).map f≤(SemidirectProduct.inl:C5→*SemidirectProduct C5 C4 φ).range:=by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    rintro x ⟨e,he,rfl⟩
    exact hEkill he
  have lift_bound (X Y N:Subgroup G) (hXP:X≤P) (hYP:Y≤P) (hb:⁅X,Y⁆≤N) :
      ⁅X.subgroupOf P,Y.subgroupOf P⁆≤N.subgroupOf P:=by
    intro t ht
    apply hb
    rw [←commutator_subgroupOf_map_eq P Y X hYP hXP]
    exact mem_map_of_mem P.subtype ht
  have hnC:(C.subgroupOf P)≤(V.subgroupOf P)⊔Q.subgroupOf P:=by
    rw [←subgroupOf_sup hVP hQP]
    exact fun _ hc=>hCjoin hc
  have hnCV:⁅C.subgroupOf P,V.subgroupOf P⁆=⊥:=by
    apply map_injective P.subtype_injective
    rw [commutator_subgroupOf_map_eq P V C hVP hCP,Subgroup.map_bot,hCV]
  obtain ⟨hCQ,hCE⟩:=commutator_residual_le_of_two_reflections φ f
    (Q.subgroupOf P) (A.subgroupOf P) (C.subgroupOf P) (V.subgroupOf P) (Vp.subgroupOf P) (E.subgroupOf P)
    hker (fun _ ha=>hAQ ha) hnC hnCV (lift_bound C Vp A hCP hVpP hCVp)
    (lift_bound Q Q A hQP hQP hQQ) hEimage hVcard hVpcard himages
  refine ⟨?_,?_⟩
  · intro c hc
    exact hCQ (show (⟨c,hCP hc⟩:P)∈C.subgroupOf P from hc)
  · have hh:=map_mono (f:=P.subtype) hCE
    rw [commutator_subgroupOf_map_eq P E C hEP hCP,map_subgroupOf_eq_of_le hAP] at hh
    exact hh

private theorem first_residual_full
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,EAt ctx.Γ ctx.criticalPath.firstStep⁆=VAt ctx.Γ ctx.criticalPath.firstStep:=by
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
  let equiv:=MulAut.conj (mover:G)⁻¹
  have hVmap:(VAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom=VAt ctx.Γ ctx.criticalPath.a':=by
    change (v ctx.Γ ctx.criticalPath.firstStep).map _=v ctx.Γ ctx.criticalPath.a'
    rw [←v_act,hmove]
  have hEmap:(EAt ctx.Γ ctx.criticalPath.firstStep).map equiv.toMonoidHom=EAt ctx.Γ ctx.criticalPath.a':=by
    change (ctx.Γ.twoResidualAt _).map _=ctx.Γ.twoResidualAt _
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoResidualAt_def]
    change (twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.firstStep)).map _=
      twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')
    rw [←hmove,stabilizer_act,conjugateBy,twoResidualIn_map_equiv]
  apply map_injective (f:=equiv.toMonoidHom) equiv.injective
  rw [map_commutator,hVmap,hEmap]
  exact ten_one_large_terminal_residual_full ctx middle hpath hno

public theorem ten_one_large_predecessor_centralizes_first
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous:ctx.Γ.Vertex) (hadj:ctx.Γ.adjacent ctx.criticalPath.a previous)
    (hne:previous≠ctx.criticalPath.firstStep)
    (hreverse:¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a') :
    (QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G))⊓QAt ctx.Γ previous≤
      centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G):=by
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let E:=EAt ctx.Γ ctx.criticalPath.firstStep
  let Z:=ZAt ctx.Γ ctx.criticalPath.firstStep
  let C:=(QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G))⊓QAt ctx.Γ previous
  obtain ⟨hCQ,hCE⟩:=predecessor_first_residual_bound ctx middle hpath hno previous hadj hne hreverse
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hAC:⁅A,C⁆≤Z:=(commutator_mono le_rfl hCQ).trans_eq
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort ctx.criticalPath.firstStep
      ⟨1,ctx.Γ.act_one _⟩).2.1
  have hEP:E≤GAt ctx.Γ ctx.criticalPath.firstStep:=by
    change ctx.Γ.twoResidualAt _≤ctx.Γ.stabilizer _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hZE:⁅Z,E⁆=⊥:=by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hEP.trans (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩)
  let _ : IsElementaryAbelian 2 A:=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  have hECA:⁅⁅E,C⁆,A⁆=⊥:=by
    apply bot_unique
    rw [commutator_comm E C]
    exact (commutator_mono hCE le_rfl).trans_eq (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer A))
  have hCAE:⁅⁅C,A⁆,E⁆=⊥:=by
    apply bot_unique
    rw [commutator_comm C A]
    exact (commutator_mono hAC le_rfl).trans_eq hZE
  have hh:⁅⁅A,E⁆,C⁆=⊥:=commutator_commutator_eq_bot_of_rotate hECA hCAE
  have hfull:⁅A,E⁆=A:=first_residual_full ctx middle hpath hno
  rw [hfull,commutator_comm] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh
end Stellmacher.SectionTen
