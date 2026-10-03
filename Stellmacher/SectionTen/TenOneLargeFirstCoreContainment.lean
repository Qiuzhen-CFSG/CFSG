module
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius
public import Stellmacher.SectionTen.TenOneLargeMutualCentralizers
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# The terminal module centralizer lies in the first core supplement

In the large branch of Stellmacher (10.1), the centralizer of the terminal
module inside its two-core lies in the product of that module and the
first-step two-core. The theorem uses only the original ambient context,
offset-two middle vertex, and no-transvection hypothesis. A companion
records that the terminal module has relative index two over its
intersection with the first core.

The centralizer is a two-group centralizing the middle center, so the
actual middle local kernel puts it in the middle core and hence in the
first stabilizer. Its commutators with the first module lie in the terminal
module by the mutual-centralizer identity. The terminal centralizer fixes
these commutators, and the first module has exponent two. Consequently
every square centralizes the first module and lies in the first core.

In the established first Frobenius quotient of order twenty, its image is
therefore elementary abelian of order at most two. The terminal module is
contained in this centralizer and has nontrivial quotient image by the
actual critical-path noncontainment. The two images coincide, and lifting
through the exact native first-core kernel gives the claimed containment.
The order of this same nontrivial image gives the companion relative index.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1),
printed p.65 immediately after (20). This is the first containment used
in the subsequent predecessor intersection and final core-index bound.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem first_core_containment_and_terminal_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QAt ctx.Γ ctx.criticalPath.a' ⊓
        centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊔ QAt ctx.Γ ctx.criticalPath.firstStep ∧
    (QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      (VAt ctx.Γ ctx.criticalPath.a') = 2 := by
  classical
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let R:=QAt ctx.Γ ctx.criticalPath.firstStep
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let Pe:=GAt ctx.Γ ctx.criticalPath.a'
  let Q:=QAt ctx.Γ ctx.criticalPath.a'
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let C:=Q⊓centralizer (V:Set G)
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  let _ : IsElementaryAbelian 2 A:=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  let _ : IsElementaryAbelian 2 V:=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hshort).2.2.1
  obtain ⟨horbit,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hQmid:Q≤GAt ctx.Γ middle:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2
  have hCtwo:IsPGroup 2 C:=nine_seven_subgroup_isTwoGroup_of_le_vertex_core
    ctx.Γ ctx.criticalPath.a' C inf_le_left
  have hCmid:C≤QAt ctx.Γ middle:=nine_three_orbit_pgroup_centralizer
    ctx.toLocalContext.toSectionNineLocalContext middle horbit C hCtwo
      (inf_le_left.trans hQmid)
      (inf_le_right.trans (centralizer_le
        (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))))
  have hQmP:QAt ctx.Γ middle≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hCP:C≤P:=hCmid.trans hQmP
  have hVQ:V≤Q:=neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _
  have hVC:V≤C:=le_inf hVQ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hVP:V≤P:=hVC.trans hCP
  have hPeV:Pe≤normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hNC:normalizer (V:Set G)≤normalizer (centralizer (V:Set G):Set G):=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (normal_subgroupOf_centralizer_normalizer _)
  have hPeC:Pe≤normalizer (C:Set G):=
    (le_inf (stabilizer_le_normalizer_q ctx.Γ _) (hPeV.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hAPe:A≤Pe:=(lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hCA:C≤normalizer (A:Set G):=hCP.trans (stabilizer_le_normalizer_v ctx.Γ _)
  have hcommA:⁅C,A⁆≤A:=le_normalizer_iff_commutator_le_right.mp hCA
  have hcommV:⁅C,A⁆≤V:=by
    have hb:⁅C,A⁆≤A⊓centralizer (V:Set G):=le_inf hcommA
      ((le_normalizer_iff_commutator_le_left.mp (hAPe.trans hPeC)).trans inf_le_right)
    rw [(ten_one_large_mutual_centralizers ctx middle hpath hno).1] at hb
    exact hb.trans inf_le_right
  have hsquare (c:G) (hc:c∈C):c^2∈R:=by
    apply nine_three_module_centralizer_core_at_vertex ctx.toAmbientSectionNineContext
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hca:⁅c,a⁆∈⁅C,A⁆:=commutator_mem_commutator hc ha
    have hfix:c*⁅c,a⁆*c⁻¹=⁅c,a⁆:=by
      have hh:⁅c,a⁆*c=c*⁅c,a⁆:=mem_centralizer_iff.mp hc.2 _ (hcommV hca)
      rw [←hh,mul_inv_cancel_right]
    have hp:⁅c,a⁆^2=1:=elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=A) _ (hcommA hca)
    have hz:⁅c^2,a⁆=1:=by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hfix,←pow_two,hp]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  obtain ⟨φ,_hfaith,projection,hsurj,hkernel⟩:=ten_one_large_first_frobenius ctx middle hpath hno
  let model:=SemidirectProduct C5 C4 φ
  let _ : Finite model:=Finite.of_surjective projection hsurj
  let f:C→*model:=projection.comp (inclusion hCP)
  let K:=f.range
  have hpow:∀k:K,k^2=1:=by
    rintro ⟨_,c,rfl⟩
    apply Subtype.ext
    change f c^2=1
    rw [←map_pow]
    change projection (inclusion hCP (c^2))=1
    rw [←MonoidHom.mem_ker,hkernel]
    exact hsquare c c.property
  have hel:IsElementaryAbelian 2 K:={
    toIsMulCommutative:=⟨⟨fun x y=>(Commute.of_orderOf_dvd_two
      (fun k=>orderOf_dvd_iff_pow_eq_one.mpr (hpow k)) x y).eq⟩⟩
    exponent_dvd_p:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hKcard:Nat.card K≤2:=SemidirectProduct.elementary_two_subgroup_card_le_two φ K hel
  let J:=(V.subgroupOf P).map projection
  have hJK:J≤K:=by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨⟨v,hVC hv⟩,rfl⟩
  have hJne:J≠⊥:=by
    intro hb
    apply (sectionTenOpeningData ctx middle hpath).terminal_noncontainment
    intro v hv
    have hh:projection (⟨v,hVP hv⟩:P)∈J:=mem_map_of_mem projection hv
    have hzero:projection (⟨v,hVP hv⟩:P)=1:=hb.le hh
    have hk:(⟨v,hVP hv⟩:P)∈projection.ker:=hzero
    rw [hkernel] at hk
    exact hk
  have hJlow:2≤Nat.card J:=by
    have hh:1<Nat.card J:=(one_lt_card_iff_ne_bot J).mpr hJne
    omega
  have hKJ:K≤J:=(Subgroup.eq_of_le_of_card_ge hJK (hKcard.trans hJlow)).symm.le
  have hJcard:Nat.card J=2:=le_antisymm
    ((Nat.card_le_card_of_injective (Subgroup.inclusion hJK) (Subgroup.inclusion_injective hJK)).trans hKcard) hJlow
  constructor
  · intro c hc
    have hcK:f (⟨c,hc⟩:C)∈K:=MonoidHom.mem_range.mpr ⟨⟨c,hc⟩,rfl⟩
    obtain ⟨v,hv,heq⟩:=hKJ hcK
    have hr:v/(⟨c,hCP hc⟩:P)∈projection.ker:=
      (MonoidHom.div_mem_ker_iff projection).mpr heq
    rw [hkernel] at hr
    have hrG:(v:G)/c∈R:=hr
    have hinv:c/(v:G)∈R:=by simpa only [inv_div] using R.inv_mem hrG
    have hm:=(V⊔R).mul_mem (mem_sup_right hinv) (mem_sup_left hv)
    change c/(v:G)*(v:G)∈V⊔R at hm
    simpa only [div_mul_cancel] using hm
  · rw [←Subgroup.relIndex_subgroupOf hVP,←hkernel,Subgroup.relIndex_ker]
    exact hJcard

public theorem ten_one_large_first_core_containment
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QAt ctx.Γ ctx.criticalPath.a' ⊓
        centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊔ QAt ctx.Γ ctx.criticalPath.firstStep :=
  (first_core_containment_and_terminal_index ctx middle hpath hno).1

public theorem ten_one_large_terminal_first_core_relIndex
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    (QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      (VAt ctx.Γ ctx.criticalPath.a') = 2 :=
  (first_core_containment_and_terminal_index ctx middle hpath hno).2

end Stellmacher.SectionTen
