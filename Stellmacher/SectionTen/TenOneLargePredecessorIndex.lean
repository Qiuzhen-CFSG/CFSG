module
public import Stellmacher.SectionTen.TenOneLargeCoreCentralizerSupplement
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Stellmacher.SectionTen.TenOneLargeFirstCoreContainment
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct
public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# The terminal module centralizer has index at most two over its module

Retain the actual large Section Ten context and a predecessor adjacent to
its initial vertex, distinct from the first step, with both center/core
escapes. If the terminal module centralizer C inside the terminal two-core
satisfies C∩Q_previous≤V_terminal, then [C:V_terminal]≤2. The independent
central-layer argument supplies this containment for the final core bound.

Write V=V_terminal, R=Q_first, J=V∩R, L=C∩R and K=Q_initial∩L.
Source (15) and the actual middle swap give [V:J]=2. The subgroup J
escapes the initial core: otherwise an original critical-center actor fixes
this coatom, and the literal quotient fixed-coatom estimate and faithful
kernel force a transvection, contrary to the large-branch hypothesis.
The proved first-core containment gives C=V L. The cubic initial edge
index and J≤L cancel their common factor two, reducing [C:V] to [K:K∩V].

The actual predecessor Frobenius quotient bounds the image of K by four.
The terminal center lies in K∩V and escapes Q_previous, providing a factor
of at least two inside that image. The supplied containment places its
kernel inside V, so the index tower gives the required bound. All graph
vertices, ambient embedding and quotient instances remain those of the
original context; no further core-index or reverse-criticality premise is
introduced.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.65,
the final index sentence after (20). The proof derives the sufficient
inequality from the predecessor quotient instead of requiring the exact
intermediate quotient order printed there.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem terminal_seed_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    (QAt ctx.Γ ctx.criticalPath.firstStep).relIndex (VAt ctx.Γ ctx.criticalPath.a')=2 := by
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  obtain ⟨hres,_⟩:=ten_one_large_first_residual_index ctx middle hpath hno
  have hindex : U.relIndex A=2:=by
    have hh:=((A⊓U).subgroupOf A).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A⊓U≤A from inf_le_left)).toEquiv] at hh
    change (A⊓U).relIndex A*Nat.card (A⊓U:Subgroup G)=Nat.card A at hh
    rw [inf_relIndex_left] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hres)
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hdiv : (QAt ctx.Γ ctx.criticalPath.a').relIndex A∣2:=
    hindex ▸ relIndex_dvd_of_le_left A hUQ
  have hseed : (QAt ctx.Γ ctx.criticalPath.a').relIndex A=2:=by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone|htwo
    · exact ((sectionTenOpeningData ctx middle hpath).first_noncontainment
        (relIndex_eq_one.mp hone)).elim
    · exact htwo
  obtain ⟨_,hfirst,hterminal,hne⟩:=sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨g,_,hgfirst,hgend⟩:=ten_one_neighbor_pair_alignment ctx middle hpath
    hterminal hfirst hne.symm
  have hh : (QAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.a')).relIndex
      (VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))=2:=by
    rw [QAt,VAt,q_act,v_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hseed
  rwa [hgend,hgfirst] at hh

private theorem terminal_seed_escapes_initial
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ¬VAt ctx.Γ ctx.criticalPath.a'⊓QAt ctx.Γ ctx.criticalPath.firstStep≤
      QAt ctx.Γ ctx.criticalPath.a := by
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let J:=V⊓QAt ctx.Γ ctx.criticalPath.firstStep
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,_⟩:=nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  let _:=hN
  let _:=hW
  have hdata:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  obtain ⟨a,ha,hout⟩:=SetLike.not_le_iff_exists.mp ctx.criticalPath.critical.2
  have haA : a∈VAt ctx.Γ ctx.criticalPath.firstStep:=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1 ha
  have haP : a∈P:=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 haA
  have hZV : Z≤V:=by
    obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
    exact (ten_one_large_terminal_residual_centralizer ctx middle hpath hno).symm.le.trans inf_le_left
  intro hJ
  have hZaC : ZAt ctx.Γ ctx.criticalPath.a≤centralizer (QAt ctx.Γ ctx.criticalPath.a:Set G):=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hcomm : ⁅J,zpowers a⁆≤Z:=by
    apply (show ⁅J,zpowers a⁆=⊥ from ?_).le.trans bot_le
    rw [commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_iff.mp ((zpowers_le.mpr (hZaC ha)).trans (centralizer_le hJ))
  have hJindex : J.relIndex V∣2:=by
    rw [show J.relIndex V=(QAt ctx.Γ ctx.criticalPath.firstStep).relIndex V from inf_relIndex_left _ _,
      terminal_seed_index ctx middle hpath hno]
  have hbound:=quotient_commutator_card_le_two_of_fixed_coatom P V Z J hZV
    (stabilizer_le_normalizer_v ctx.Γ _) hN hW action hformula ⟨a,haP⟩ inf_le_left hJindex hcomm
  let D:=⁅V,zpowers a⁆⊔Z
  change Z.relIndex D≤2 at hbound
  have hnot : Z.relIndex D≠1:=by
    intro hone
    exact hout ((hdata.2.2 a haP).mp (le_sup_left.trans (relIndex_eq_one.mp hone)))
  have hpos : Z.relIndex D≠0:=(Z.subgroupOf D).index_ne_zero_of_finite
  have htwo : Z.relIndex D=2:=by omega
  apply hno a haA hout
  have hh:=(Z.subgroupOf D).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Z≤D from le_sup_right)).toEquiv] at hh
  change Z.relIndex D*Nat.card Z=Nat.card D at hh
  exact htwo ▸ hh.symm

omit [Finite G] in
private theorem two_subgroup_index_le_four
    (P R K : Subgroup G) (hK : K≤P) (hKtwo : IsPGroup 2 K)
    (hmodel : QuotientIsFrobenius20 P R) : R.relIndex K≤4 := by
  obtain ⟨φ,_,projection,_,hkernel⟩:=hmodel
  let model:=SemidirectProduct C5 C4 φ
  let _ : Finite model:=Finite.of_equiv (C5×C4) SemidirectProduct.equivProd.symm
  let f:K→*model:=projection.comp (inclusion hK)
  have hfker : f.ker=R.subgroupOf K:=by
    ext x
    change projection ⟨(x:G),hK x.property⟩=1 ↔ (x:G)∈R
    rw [←MonoidHom.mem_ker,hkernel]
    rfl
  have htwo : IsPGroup 2 f.range:=hKtwo.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard : Nat.card model=20:=by
    rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod]
    norm_num [C5,C4,Nat.card_zmod]
  have hdiv : Nat.card f.range∣20:=hcard ▸ f.range.card_subgroup_dvd_card
  obtain ⟨n,hn⟩:=htwo.exists_card_eq
  have hle : Nat.card f.range≤20:=Nat.le_of_dvd (by decide) hdiv
  have hpowbound : 2^n≤20:=hn ▸ hle
  have hnle : n≤4:=by
    by_contra hh
    have hp : 2^5≤2^n:=Nat.pow_le_pow_right (by decide) (by omega)
    norm_num only [Nat.reducePow] at hp
    omega
  have hbound : Nat.card f.range≤4:=by
    rw [hn] at hdiv ⊢
    interval_cases n
    all_goals norm_num at hdiv
    all_goals norm_num
  have hi:=index_ker f
  rw [hfker] at hi
  exact hi.trans_le hbound

private theorem predecessor_two_subgroup_index_le_four
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent ctx.criticalPath.a previous)
    (K : Subgroup G) (hK : K≤GAt ctx.Γ previous) (hKtwo : IsPGroup 2 K) :
    (QAt ctx.Γ previous).relIndex K≤4 := by
  obtain ⟨g,hg⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.a ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)
  let e:=MulAut.conj (g:G)⁻¹
  have hPmap : (GAt ctx.Γ previous).map e.toMonoidHom=GAt ctx.Γ ctx.criticalPath.firstStep:=by
    change conjugateBy (stabilizer ctx.Γ previous) (g:G)⁻¹=_
    rw [←stabilizer_act,hg]
  have hQmap : (QAt ctx.Γ previous).map e.toMonoidHom=QAt ctx.Γ ctx.criticalPath.firstStep:=by
    change (q ctx.Γ previous).map e.toMonoidHom=_
    rw [←q_act,hg]
  have hKmap : K.map e.toMonoidHom≤GAt ctx.Γ ctx.criticalPath.firstStep:=
    (map_mono hK).trans hPmap.le
  have hb:=two_subgroup_index_le_four (GAt ctx.Γ ctx.criticalPath.firstStep)
    (QAt ctx.Γ ctx.criticalPath.firstStep) (K.map e.toMonoidHom) hKmap
    (hKtwo.map e.toMonoidHom) (ten_one_large_first_frobenius ctx middle hpath hno)
  rw [←hQmap,relIndex_map_map_of_injective _ _ e.injective] at hb
  exact hb

public theorem ten_one_large_centralizer_index_of_predecessor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (previous : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent ctx.criticalPath.a previous)
    (_hne : previous≠ctx.criticalPath.firstStep)
    (hforward : ¬ZAt ctx.Γ ctx.criticalPath.a'≤QAt ctx.Γ previous)
    (_hreverse : ¬ZAt ctx.Γ previous≤QAt ctx.Γ ctx.criticalPath.a')
    (hcontain : (QAt ctx.Γ ctx.criticalPath.a'⊓centralizer
      (VAt ctx.Γ ctx.criticalPath.a':Set G))⊓QAt ctx.Γ previous≤VAt ctx.Γ ctx.criticalPath.a') :
    (VAt ctx.Γ ctx.criticalPath.a').relIndex
      (QAt ctx.Γ ctx.criticalPath.a'⊓centralizer (VAt ctx.Γ ctx.criticalPath.a':Set G))≤2 := by
  have hfirstContainment:=ten_one_large_first_core_containment ctx middle hpath hno
  let Γ:=ctx.Γ
  let cp:=ctx.criticalPath
  let P:=GAt Γ cp.firstStep
  let R:=QAt Γ cp.firstStep
  let Qa:=QAt Γ cp.a
  let V:=VAt Γ cp.a'
  let Z:=ZAt Γ cp.a'
  let C:=QAt Γ cp.a'⊓centralizer (V:Set G)
  let J:=V⊓R
  let L:=C⊓R
  let K:=Qa⊓L
  let Rprev:=QAt Γ previous
  have hshort : 1<cp.length:=by change 1<ctx.criticalPath.length;rw [ctx.critical_length];decide
  have hlong : 2<cp.length:=by change 2<ctx.criticalPath.length;rw [ctx.critical_length];decide
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hVQmid : V≤QAt Γ middle:=
    (show V≤GeneratedNeighborhoodV Γ middle from le_sSup
      ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle)
  have hVP : V≤P:=hVQmid.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2)
  have hRP : R≤P:=by
    change Γ.twoCoreAt cp.firstStep≤P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hRN : (R.subgroupOf P).Normal:=by
    change ((Γ.twoCoreAt cp.firstStep).subgroupOf P).Normal
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_normal _
  let _:=hRN
  have hCP : C≤P:=hfirstContainment.trans (sup_le hVP hRP)
  let _ : IsElementaryAbelian 2 V:=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hshort).2.2.1
  have hVC : V≤C:=le_inf (neighbor_join_le_core_of_length_gt_one Γ cp hshort _)
    (le_centralizer V)
  have hLC : L≤C:=inf_le_left
  have hfactor : C=V⊔L:=by
    apply le_antisymm ?_ (sup_le hVC hLC)
    intro c hc
    have hcP : (⟨c,hCP hc⟩:P)∈V.subgroupOf P⊔R.subgroupOf P:=by
      rw [←subgroupOf_sup hVP hRP]
      exact hfirstContainment hc
    obtain ⟨v,hv,r,hr,heq⟩:=mem_sup_of_normal_right.mp hcP
    have heqG : (v:G)*(r:G)=c:=congrArg (fun x:P=>(x:G)) heq
    have hrC : (r:G)∈C:=by
      have hh:=C.mul_mem (C.inv_mem (hVC hv)) hc
      change (v:G)⁻¹*c∈C at hh
      rw [←heqG,←mul_assoc,inv_mul_cancel,one_mul] at hh
      exact hh
    rw [←heqG]
    exact (V⊔L).mul_mem (mem_sup_left hv) (mem_sup_right ⟨hrC,hr⟩)
  let _ : (V.subgroupOf C).Normal:=
    (normal_subgroupOf_iff_le_normalizer hVC).mpr
      ((show C≤centralizer (V:Set G) from inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
  have hindexC : V.relIndex C=V.relIndex L:=by
    have hh:=relIndex_sup_left (L.subgroupOf C) (V.subgroupOf C)
    rw [←subgroupOf_sup hVC hLC,←hfactor,subgroupOf_self,relIndex_top_right,
      relIndex_subgroupOf hLC] at hh
    exact hh
  have hQaEdge : Qa.relIndex (GAt Γ cp.a⊓P)=2:=by
    have hcard:=(nine_initial_edge_core_product ctx.toAmbientSectionNineContext hshort).2
    have hQaE : Qa≤GAt Γ cp.a⊓P:=
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
    have hh:=(Qa.subgroupOf (GAt Γ cp.a⊓P)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQaE).toEquiv] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hcard)
  have hLEdge : L≤GAt Γ cp.a⊓P:=inf_le_right.trans
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers)
  have hLbound : Qa.relIndex L≤2:=by
    rw [←hQaEdge]
    exact relIndex_le_of_le_right hLEdge (Qa.subgroupOf _).index_ne_zero_of_finite
  have hJL : J≤L:=inf_le_inf_right R hVC
  have hJbound : Qa.relIndex J≤Qa.relIndex L:=
    relIndex_le_of_le_right hJL (Qa.subgroupOf L).index_ne_zero_of_finite
  have hJnot : Qa.relIndex J≠1:=fun heq=>terminal_seed_escapes_initial ctx middle hpath hno
    (relIndex_eq_one.mp heq)
  have hJpos : Qa.relIndex J≠0:=(Qa.subgroupOf J).index_ne_zero_of_finite
  have hJtwo : Qa.relIndex J=2:=by omega
  have hLtwo : Qa.relIndex L=2:=by omega
  have hcancel : V.relIndex K=V.relIndex L:=by
    have h1:=relIndex_inf_mul_relIndex V Qa L
    have h2:=relIndex_inf_mul_relIndex Qa V L
    have hVL : V⊓L=J:=by
      apply le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      intro x hx
      exact ⟨hx.1,hVC hx.1,hx.2⟩
    rw [hVL,hJtwo,inf_comm Qa V] at h2
    rw [hLtwo] at h1
    change V.relIndex K*2=_ at h1
    omega
  have hKprev : K≤GAt Γ previous:=inf_le_left.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent Γ).mpr hadj) default).2.2)
  have hKtwo : IsPGroup 2 K:=nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ cp.a K inf_le_left
  have hKbound : Rprev.relIndex K≤4:=
    predecessor_two_subgroup_index_le_four ctx middle hpath hno previous hadj K hKprev hKtwo
  have hZV : Z≤V:=(ten_one_large_terminal_residual_centralizer ctx middle hpath hno).symm.le.trans inf_le_left
  have hZR : Z≤R:=by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    have hh:=path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [cp.path_first,cp.path_end] at hh
    change Γ.distance cp.firstStep cp.a'<cp.length
    have hlen : cp.length=3:=ctx.critical_length
    omega
  have hZQa : Z≤Qa:=by
    change Z≤q Γ cp.a
    rw [←(lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer]
    exact le_inf (hZR.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ctx.commutator_eq))
  have hZK : Z≤K:=le_inf hZQa (le_inf (hZV.trans hVC) hZR)
  let I:=V⊓K
  have hZI : Z≤I:=le_inf hZV hZK
  have hIpos : Rprev.relIndex I≠0:=(Rprev.subgroupOf I).index_ne_zero_of_finite
  have hInot : Rprev.relIndex I≠1:=fun heq=>hforward (hZI.trans (relIndex_eq_one.mp heq))
  have hIlower : 2≤Rprev.relIndex I:=by omega
  have hRI : Rprev⊓K≤I:=by
    intro x hx
    exact ⟨hcontain ⟨hx.2.2.1,hx.1⟩,hx.2⟩
  have hRKeq : Rprev⊓K=Rprev⊓I:=le_antisymm
    (le_inf inf_le_left hRI) (inf_le_inf_left Rprev (show I≤K from inf_le_right))
  have htower:=relIndex_mul_relIndex (Rprev⊓K) I K hRI inf_le_right
  have hRIindex : (Rprev⊓K).relIndex I=Rprev.relIndex I:=by rw [hRKeq,inf_relIndex_right]
  rw [hRIindex] at htower
  have hIindex : I.relIndex K=V.relIndex K:=inf_relIndex_right _ _
  rw [hIindex,inf_relIndex_right] at htower
  rw [hindexC,←hcancel]
  nlinarith

end Stellmacher.SectionTen
