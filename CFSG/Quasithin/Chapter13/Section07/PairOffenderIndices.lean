module

public import CFSG.Quasithin.Chapter13.Section07.PairStrictD

/-!
# Original candidate images and fixed-index bounds

The two exchanged seed intersections have equal relative indices. Their
proved centralization and the strict intersection theorem give the fixed
index bounds for both original candidate subgroups. Squares in the second
core factor lie in the actual radical, so its image is elementary; the
conjugate seed image makes it nontrivial.
Source: Aschbacher--Smith13.7.11--12(3), printed pp.941--942.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The original relative-index inequalities for both source offender candidates. -/
theorem pair_seed_fixed_index_bounds
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let Ug:=conjugate F.UH (g:G)
    let A:=conjugate F.VH (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    (F.UH⊓centralizer (A:Set G)).relIndex F.UH≤F.QH.relIndex A ∧
    (F.UH⊓centralizer (Ug:Set G)).relIndex F.UH≤F.QH.relIndex Ug ∧
    1<F.QH.relIndex Ug := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U:=F.UH
  let Ug:=conjugate U (g:G)
  let A:=conjugate F.VH (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  have hUQ:U≤(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2:=
    (le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  have hD:F.DH (g:G)≤U⊓centralizer (A:Set G):=le_inf inf_le_left
    (commutator_eq_bot_iff_le_centralizer.mp
      (ConjugateIntersections.lemma_13_7_10_six h g hs hUQ hout (centralizer_UH_commutator d h)).2.2.1)
  have hr:(F.DH (g:G)).relIndex U=F.QH.relIndex Ug := by
    have hm:=relIndex_map_map_of_injective (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) (F.DH (g:G)) U (MulAut.conj (g:G)⁻¹).injective
    change (conjugate (F.DH (g:G)) (g:G)).relIndex Ug=(F.DH (g:G)).relIndex U at hm
    rw [(h.intersection_exchange_of_core_quotient_square g hs).1] at hm
    change (Ug⊓F.QH).relIndex Ug=(F.DH (g:G)).relIndex U at hm
    rw [inf_relIndex_left] at hm
    exact hm.symm
  obtain ⟨hUgA,_,hnot,_⟩:=pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hDC:F.DH (g:G)≤U⊓centralizer (Ug:Set G):=
    hD.trans (inf_le_inf_left _ (centralizer_le hUgA))
  have hbound:(U⊓centralizer (A:Set G)).relIndex U≤F.QH.relIndex Ug :=
    (relIndex_le_of_le_left hD (by exact Subgroup.index_ne_zero_of_finite)).trans_eq hr
  have hboundU:(U⊓centralizer (Ug:Set G)).relIndex U≤F.QH.relIndex Ug :=
    (relIndex_le_of_le_left hDC (by exact Subgroup.index_ne_zero_of_finite)).trans_eq hr
  refine ⟨hbound.trans (relIndex_le_of_le_right hUgA (by exact Subgroup.index_ne_zero_of_finite)),hboundU,?_⟩
  have hpos:0<F.QH.relIndex Ug:=Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hne:F.QH.relIndex Ug≠1:=fun he=>hnot (relIndex_eq_one.mp he)
  change 1<F.QH.relIndex Ug
  omega


/-- The original second core factor has a nontrivial elementary image in H/O₂(H). -/
theorem pair_actor_elementary_nontrivial
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let A:=conjugate F.VH (g:G)⊓Q
    let q:=QuotientGroup.mk' (pCore 2 H)
    A≤H ∧ IsElementaryAbelian 2 ((A.subgroupOf H).map q) ∧
      (A.subgroupOf H).map q≠⊥ := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let A:=conjugate F.VH (g:G)⊓Q
  let q:=QuotientGroup.mk' (pCore 2 H)
  have hAH:A≤H:=inf_le_right.trans
    ((h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H)
  have hgV:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hp:conjugate V₁ (g:G)≤F.QH:=
    (map_mono (h.point_lt.le.trans h.plus_le)).trans (hgV.le.trans
      ((le_conjugateSpanBy V H).trans (VH_le_core d h hU)))
  have hsquare:∀a:A,(q ⟨a,hAH a.property⟩)^2=1 := by
    intro a
    have ha:a.val∈conjugate F.VH (g:G):=a.property.1
    obtain ⟨b,hb,he⟩:=ha
    have hs0:a.val^2∈conjugate V₁ (g:G) := by
      rw [←he,←map_pow]
      exact mem_map_of_mem _ (square_VH_mem_point d h hU hb)
    have hsQ:a.val^2∈F.QH:=hp hs0
    have hsH:(⟨a,hAH a.property⟩:H)^2∈pCore 2 H := by
      obtain ⟨b,hb,he⟩:=hsQ
      have hh:b=(⟨a,hAH a.property⟩:H)^2:=Subtype.ext he
      exact hh ▸ hb
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hsH
  let B:Subgroup (H⧸pCore 2 H):=(A.subgroupOf H).map q
  have hpow:∀b:B,b^2=1 := by
    intro b
    obtain ⟨a,ha,he⟩:=b.property
    apply Subtype.ext
    change (b:H⧸pCore 2 H)^2=1
    rw [←he]
    exact hsquare ⟨a,ha⟩
  have hEA:IsElementaryAbelian 2 B := {
    is_comm:=⟨fun a b=>(Commute.of_orderOf_dvd_two (fun x=>orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩
    exponent_dvd_p:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hne:B≠⊥ := by
    intro hb
    obtain ⟨hUgA,_,_,hne⟩:=pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
    exact hne (bot_unique ((map_mono (comap_mono hUgA)).trans hb.le))
  exact ⟨hAH,hEA,hne⟩

end CFSG.Quasithin.Chapter13.Section07
