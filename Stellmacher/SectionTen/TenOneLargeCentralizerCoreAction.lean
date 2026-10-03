module
public import Stellmacher.SectionTen.TenOneLargeCentralizerSetup
public import Theory.GroupAction.QuotientCommutatorPairing
public import Theory.GroupAction.QuotientCommutatorFamily
public import Stellmacher.SectionTen.TenOneLargeTerminalIrreducible

/-!
# Central residual-core action on the source-(16) enlargement

In the actual no-transvection Section Ten context, let Y be C_W(Vend)
joined with the omega-one center of the middle neighborhood group. The
commutator of YVend with O₂(Eend) lies in Zend. The proof constructs and
retains the actual terminal quotient action; no source-(16) centralizer
equality or later Frobenius quotient model is assumed.

The established middle-section bound puts the quotient commutator image
of U∩Qmiddle inside I/Z, of order four. That section has index two in U,
so each individual cyclic image has order at most eight. On the terminal
quotient of order sixteen, the genuine stabilizer action is irreducible.
The quotient commutator-family theorem uses the two-group action on the
family and forces every image to be trivial. Lifting gives the asserted
central-line bound.

This is the small-image inference before Stellmacher (10.1)(16), Journal
of Algebra 190 (1997), printed p.64. The later fixed-component and local
centralizer-transitivity arguments are separate steps.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem small_images
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))] :
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let Z:=ZAt ctx.Γ ctx.criticalPath.a'
    let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
    ∀ b:(Y⊔V:Subgroup G),
      Nat.card ((⁅Subgroup.zpowers (b:G),twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆.subgroupOf V).map
        (QuotientGroup.mk' (Z.subgroupOf V)))≤8 := by
  dsimp only
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let I:=A⊓V
  let W:=conjugateClosure (A⊓QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  let Wnext:=GeneratedNeighborhoodV ctx.Γ middle
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔omegaOneCenter Wnext
  let BB:=Y⊔V
  let K:=U⊓QAt ctx.Γ middle
  let Vbar:=V⧸Z.subgroupOf V
  let π:=QuotientGroup.mk' (Z.subgroupOf V)
  obtain ⟨hBB,hYW,_hYC,_hPB,hBE,hYK,_hIO,_hOVI⟩:=ten_one_large_centralizer_setup ctx middle hpath hno
  let _ : IsElementaryAbelian 2 BB:=hBB
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcenter:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  have hZcard : Nat.card Z=2:=hcenter.1
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq hcenter.2.1
  have hBU : ⁅BB,U⁆≤V:=(Subgroup.commutator_mono le_rfl (twoCoreIn_le E)).trans hBE
  have hZI : Z≤I:=by
    have hmid:ZAt ctx.Γ middle≤I:=le_inf
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
      (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
    apply le_trans ?_ hmid
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hZV : Z≤V:=hZI.trans inf_le_right
  have hIcard : Nat.card I=8:=(ten_one_large_terminal_structure ctx middle hpath hno).2.2
  have hZIindex : Z.relIndex I=4:=by
    have hh:=(Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hh
    change Z.relIndex I*2=8 at hh
    omega
  let Ibar:=(I.subgroupOf V).map π
  have hIbarCard : Nat.card Ibar=4:=by
    have hh:=Subgroup.relIndex_ker (I.subgroupOf V) π
    rw [QuotientGroup.ker_mk'] at hh
    have hmap:=Subgroup.relIndex_map_map_of_injective (Z.subgroupOf V) (I.subgroupOf V) V.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZV,
      Subgroup.map_subgroupOf_eq_of_le (show I≤V from inf_le_right),hZIindex] at hmap
    exact hh.symm.trans hmap.symm
  have hKindex : (K.subgroupOf U).index=2:=by
    change K.relIndex U=2
    rw [Subgroup.inf_relIndex_left]
    exact ten_one_terminal_residual_middle_index ctx middle hpath
  have hVW : V≤Wnext:=le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hWP : Wnext≤GAt ctx.Γ middle:=(nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hlong middle).trans (by
      change ctx.Γ.twoCoreAt middle≤GAt ctx.Γ middle
      rw [ctx.Γ.twoCoreAt_def]
      exact twoCoreIn_le _)
  have hBK : ⁅BB,K⁆≤I:=by
    have hh:=SectionEight.eight_six_commutator_sSup_le ({Y,V}:Set (Subgroup G)) K I
      (GAt ctx.Γ middle) (ten_one_common_intersection_normalized ctx middle hpath)
      (by intro D hD;rcases hD with rfl|hD;exact hYW.trans hWP
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D;exact hVW.trans hWP)
      (by intro D hD;rcases hD with rfl|hD;exact hYK
          have : D=V:=Set.mem_singleton_iff.mp hD;subst D
          exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hVU).trans hZI)
    simpa only [sSup_pair] using hh
  let pairing:=Subgroup.quotientCommutatorPairing BB U V Z le_sup_right hBU hVU
  intro b
  let f:U→*Vbar:=pairing b
  have hKimage : (K.subgroupOf U).map f≤Ibar:=by
    rintro w ⟨k,hk,rfl⟩
    refine ⟨⟨⁅(b:G),(k:G)⁆,hBU (Subgroup.commutator_mem_commutator b.property k.property)⟩,?_,?_⟩
    · exact hBK (Subgroup.commutator_mem_commutator b.property hk)
    · exact (Subgroup.quotientCommutatorPairing_apply BB U V Z le_sup_right hBU hVU b k).symm
  have hKcard : Nat.card ((K.subgroupOf U).map f)≤4:=
    (Subgroup.card_le_of_le hKimage).trans_eq hIbarCard
  let M:=(K.subgroupOf U).map f.rangeRestrict
  have hMindex : M.index≤2:=by
    have hh:=(K.subgroupOf U).index_map_dvd f.rangeRestrict_surjective
    rw [hKindex] at hh
    exact Nat.le_of_dvd (by decide) hh
  have hMmap : M.map f.range.subtype=(K.subgroupOf U).map f:=by
    rw [Subgroup.map_map]
    rfl
  have hMcard : Nat.card M≤4:=by
    rw [←Subgroup.card_map_of_injective f.range.subtype_injective,hMmap]
    exact hKcard
  have hcount:=M.index_mul_card
  have hbound : Nat.card f.range≤8:=by nlinarith
  rw [←Subgroup.quotientCommutatorPairing_range BB U V Z le_sup_right hBU hVU b]
  exact hbound



public theorem ten_one_large_centralizer_core_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)
    let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
    ⁅Y⊔V,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆≤ZAt ctx.Γ ctx.criticalPath.a' := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let W:=conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep⊓QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ middle)
  let Y:=(W⊓Subgroup.centralizer (V:Set G))⊔omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle)
  let BB:=Y⊔V
  obtain ⟨hBB,_hYW,_hYC,hPB,hBE,_hYK,_hIO,_hOVI⟩:=ten_one_large_centralizer_setup ctx middle hpath hno
  let _ : IsElementaryAbelian 2 BB:=hBB
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hZcard,hVQ,_⟩:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  obtain ⟨hN,hW,action,hformula,hkernel⟩:=nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  let _:=hN
  let _:=hW
  have hE : E=twoResidualIn P:=by
    change ctx.Γ.twoResidualAt ctx.criticalPath.a'=twoResidualIn P
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  have hEP : E≤P:=hE ▸ twoResidualIn_le P
  have hEN : (E.subgroupOf P).Normal:=hE ▸ twoResidualIn_normal P
  let _:=hEN
  have hPU : P≤Subgroup.normalizer (U:Set G):=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ((twoCoreIn_le E).trans hEP)).mp
      (twoCoreIn_normal_of_normal E P hEP hEN)
  have hPV : P≤Subgroup.normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hPZ : P≤Subgroup.normalizer (Z:Set G):=stabilizer_le_normalizer_z ctx.Γ _
  have hptwo : IsPGroup 2 (P⧸E.subgroupOf P):=by
    have hn : E.subgroupOf P=twoResidualSubgroup P:=by
      rw [hE,twoResidualIn,twoResidualAmbient]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    have hr : E.subgroupOf P=BenderSuzuki.External.hktPResidual 2 P:=
      hn.trans (SectionThree.twoResidualSubgroup_eq_hktPResidual' P)
    let _ : (BenderSuzuki.External.hktPResidual 2 P).Normal:=
      BenderSuzuki.External.hktPResidual_normal
    exact (BenderSuzuki.External.hktPResidual_quotient_isPGroup (Q:=P) (q:=2)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hr).symm
  have hQP : QAt ctx.Γ ctx.criticalPath.a'≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hZV : Z≤V:=hVQ.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq hVQ
  have hBU : ⁅BB,U⁆≤V:=(Subgroup.commutator_mono le_rfl (twoCoreIn_le E)).trans hBE
  have hVcard : Nat.card V=32:=(ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hquotCard : Nat.card (V⧸Z.subgroupOf V)=16:=by
    have hh:=Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    omega
  exact Subgroup.commutator_le_of_small_irreducible_family P BB U V Z E hZV le_sup_right
    hPB hPU hPV hPZ hEP hptwo hBU hVU hBE action hformula
    (ten_one_large_terminal_irreducible ctx middle hpath hno action hformula hkernel)
    (fun b=>(small_images ctx middle hpath hno b).trans_lt (by rw [hquotCard];decide))

end Stellmacher.SectionTen
