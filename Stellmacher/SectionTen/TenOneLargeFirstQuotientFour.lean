module
public import Stellmacher.SectionTen.TenOneLargeFirstResidualIndex
public import Stellmacher.SectionTen.TenOneLargeNeighborhoodQuotient

/-!
# Four divides the first local core quotient in the large branch

For the original Section Ten context in the no-transvection case, the actual
quotient of the first stabilizer by its two-core has order divisible by four.
No odd residual model or source-(18) quotient cardinality is assumed.

The terminal residual core's middle coatom C has noncentral commutator with
the first module A. If C lay in V_terminal Q_first, the normal-core product
factorization would put that commutator in V_terminal, a contradiction.
Both C and V_terminal lie in the middle two-core, so their joined image in
the first core quotient is a two-group. The actual middle swap carries the
source-(15) seed index to an order-two image of V_terminal. That image is
proper in the joined image, which therefore has order divisible by four.
Lagrange gives the required divisibility for the literal local quotient.

This supplies the two-part of the Frobenius recognition in Stellmacher
(10.1)(19), printed p.64 of `refs/files/stellmacher-n-group.pdf`, using the
proved coatom argument before source (15). The later five-residual exclusion
is a separate input to the final recognition.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_first_core_quotient_four_dvd
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    4 ∣ Nat.card (GAt ctx.Γ ctx.criticalPath.firstStep ⧸
      pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)) := by
  classical
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let R:=QAt ctx.Γ ctx.criticalPath.firstStep
  let A:=VAt ctx.Γ ctx.criticalPath.firstStep
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let Qm:=QAt ctx.Γ middle
  let C:=U⊓Qm
  let W:=conjugateClosure (A⊓QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  obtain ⟨_,hfirst,hterminal,hne⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hlong : 2<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hQmP : Qm≤P:=((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hVQm : V≤Qm:=(show V≤GeneratedNeighborhoodV ctx.Γ middle from le_sSup
    ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle)
  have hVP : V≤P:=hVQm.trans hQmP
  have hCP : C≤P:=inf_le_right.trans hQmP
  have hRP : R≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hRnative : R.subgroupOf P=pCore 2 P:=by
    change (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep).subgroupOf P=pCore 2 P
    rw [ctx.Γ.twoCoreAt_def,twoCoreIn,Subgroup.subgroupOf]
    change ((pCore 2 P).map P.subtype).comap P.subtype=pCore 2 P
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  let _ : (R.subgroupOf P).Normal:=hRnative.symm ▸ inferInstance
  have hAV : A≤Subgroup.normalizer (V:Set G):=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2.trans
      (stabilizer_le_normalizer_v ctx.Γ _)
  have hZV : ZAt ctx.Γ ctx.criticalPath.firstStep≤V:=by
    apply le_trans ?_ (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_left
  have hRA : ⁅R,A⁆≤V:=by
    rw [Subgroup.commutator_comm]
    exact (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩).2.1.le.trans hZV
  have hCnot : ¬C≤V⊔R:=by
    intro hle
    apply (ten_one_large_terminal_core_commutator_escape ctx middle hpath hno).2
    apply Subgroup.commutator_le.mpr
    intro c hc a ha
    have hcP : (⟨c,hCP hc⟩:P)∈V.subgroupOf P⊔R.subgroupOf P:=by
      rw [←Subgroup.subgroupOf_sup hVP hRP]
      exact hle hc
    obtain ⟨v,hv,q,hq,heq⟩:=Subgroup.mem_sup_of_normal_right.mp hcP
    have hvq : (v:G)*(q:G)=c:=congrArg (fun x:P=>(x:G)) heq
    rw [←hvq,commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem (V.mul_mem (V.mul_mem hv
      (hRA (Subgroup.commutator_mem_commutator hq ha))) (V.inv_mem hv))
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hAV
        (Subgroup.commutator_mem_commutator hv ha))
  have hUQ : U≤QAt ctx.Γ ctx.criticalPath.a':=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  obtain ⟨hres,hWU⟩:=ten_one_large_first_residual_index ctx middle hpath hno
  have hseedEq : A⊓QAt ctx.Γ ctx.criticalPath.a'=A⊓U:=by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply le_trans ?_ hWU
      intro x hx
      exact Subgroup.subset_closure ⟨1,⟨x,hx⟩,by simp⟩
    · exact inf_le_inf_left A hUQ
  have horiginal : (QAt ctx.Γ ctx.criticalPath.a').relIndex A=2:=by
    have hh:=((A⊓U).subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A⊓U≤A from inf_le_left)).toEquiv] at hh
    change (A⊓U).relIndex A*Nat.card (A⊓U:Subgroup G)=Nat.card A at hh
    have hi : (A⊓U).relIndex A=2 := Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hres)
    rwa [←hseedEq,Subgroup.inf_relIndex_left] at hi
  have hRindex : R.relIndex V=2:=by
    obtain ⟨g,_hg,hgfirst,hgend⟩:=ten_one_neighbor_pair_alignment ctx middle hpath hterminal hfirst hne.symm
    have hh : (QAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.a')).relIndex
        (VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))=2 := by
      rw [QAt,VAt,q_act,v_act,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact horiginal
    rwa [hgend,hgfirst] at hh
  let q:P→*P⧸pCore 2 P:=QuotientGroup.mk' (pCore 2 P)
  let J:=C⊔V
  have hJQ : J≤Qm:=sup_le inf_le_right hVQm
  have hJP : J≤P:=hJQ.trans hQmP
  let D:Subgroup (P⧸pCore 2 P):=(V.subgroupOf P).map q
  let K:Subgroup (P⧸pCore 2 P):=(J.subgroupOf P).map q
  have hDcard : Nat.card D=2:=by
    change Nat.card ((V.subgroupOf P).map q)=2
    rw [←Subgroup.relIndex_ker,QuotientGroup.ker_mk',←hRnative,Subgroup.relIndex_subgroupOf hVP]
    exact hRindex
  have hDK : D≤K:=Subgroup.map_mono (fun x hx=>show (x:G)∈J from Subgroup.mem_sup_right hx)
  have hKnot : ¬K≤D:=by
    intro hKD
    apply hCnot
    intro c hc
    have hcmem : q ⟨c,hCP hc⟩∈K:=Subgroup.mem_map_of_mem q (Subgroup.mem_sup_left hc)
    obtain ⟨v,hv,hveq⟩:=hKD hcmem
    have hratio : (v:G)/c∈R:=by
      have hh:=QuotientGroup.eq_iff_div_mem.mp hveq
      change v/(⟨c,hCP hc⟩:P)∈pCore 2 P at hh
      rw [←hRnative] at hh
      exact hh
    have hinv : c/(v:G)∈R:=by simpa only [inv_div] using R.inv_mem hratio
    have hh:=(V⊔R).mul_mem (Subgroup.mem_sup_right hinv) (Subgroup.mem_sup_left hv)
    change c/(v:G)*(v:G)∈V⊔R at hh
    simpa only [div_mul_cancel] using hh
  have hKbig : 2<Nat.card K:=by
    have hle:=Subgroup.card_le_of_le hDK
    have hneq : Nat.card K≠Nat.card D:=by
      intro hc
      exact hKnot (Subgroup.eq_of_le_of_card_ge hDK hc.le).symm.le
    omega
  have hJtwo : IsPGroup 2 J:=nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ middle J hJQ
  have hKtwo : IsPGroup 2 K:=(hJtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hJP).symm).map q
  obtain ⟨n,hn⟩:=hKtwo.exists_card_eq
  have hn2 : 2≤n:=by
    have hp : 2<2^n := hn ▸ hKbig
    by_contra hh
    have : n≤1:=by omega
    interval_cases n <;> norm_num at hp
  have hfour : 4∣Nat.card K:=by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  exact hfour.trans K.card_subgroup_dvd_card
end Stellmacher.SectionTen
