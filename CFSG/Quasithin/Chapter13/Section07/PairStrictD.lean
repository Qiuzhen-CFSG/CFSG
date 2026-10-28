module

public import CFSG.Quasithin.Chapter13.Section07.PairEIntersections
public import Theory.GroupTheory.ElementaryIndexTwoSylowFixed

/-!
# The genuine nontrivial displaced seed in13.7.11

If DH equals UH, the source centralizer calculation and EH=EHg=ZI force
both core factors to equal ZI. The first factor is then elementary of
index two in VH and is normalized by the original Sylow T. Its H-orbit
has odd size and at most two elements, so H normalizes it. Since it
contains V, this contradicts VH being the nonabelian H-span of V.

Thus DH<UH, and the square-marked conjugator makes UH^g nontrivial in the
actual quotient H/O₂(H). The final consumer constructs that original g.
No extraspecial model, point-graph connectedness or13.7.4 faithfulness
conclusion is taken as an input.
Source: Aschbacher--Smith13.7.11, printed p.942.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem pair_D_lt_seed_span
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g:G)<Section08.Source.UH H V₃ := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let A:=F.VH
  let B:=conjugate A (g:G)
  let U:=F.UH
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let E:=A⊓B
  let W:=A⊓Q
  have hQT:Q≤(T:Subgroup G):=h.sylow_centralizer.symm.le.trans inf_le_left
  have hQH:Q≤H:=hQT.trans h.T_le_H
  have hUQ:U≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  apply lt_of_le_of_ne (show F.DH (g:G)≤U from inf_le_left)
  intro he
  have hc:⁅U,B⊓Q⁆=⊥ := by
    rw [←he]
    exact (ConjugateIntersections.lemma_13_7_10_six h g hs hUQ hout
      (centralizer_UH_commutator d h)).2.2.1
  have hBQ:B⊓Q≤F.QH := by
    intro z hz
    apply h.kernel_UH_eq_QH.le
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨hQH hz.2,?_⟩
    intro u hu
    have hzC:z∈centralizer (U:Set G):=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc) hz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hzC u hu)]
    exact V₁.one_mem
  obtain ⟨hVE,hES,hnE,hcomm,hEA⟩:=pair_intersection_layer d h hU g hout
  have hEQ:E≤Q:=hES.trans ((pair_twoCore_quotient d h hU hV g hout).1.le.trans inf_le_right)
  have hY:B⊓Q=E := by
    apply le_antisymm
    · have hh:B⊓Q≤F.EHg (g:G):=le_inf inf_le_left hBQ
      exact hh.trans (pair_Eg_eq_intersection d h hU hV g hs hout).le
    · exact le_inf inf_le_right hEQ
  have htwice:conjugate B (g:G)=A:=h.conjugate_twice_eq_of_square
    (le_normalizer_conjugateSpanBy V H) (h.square_mem_local_of_core_quotient_square g hs)
  have hQQ:conjugate Q (g:G)=Q:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Q:Set G)).inv_mem
      (((L⊔(T:Subgroup G):Subgroup G).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G)))) g.property))
  have hWW:W=E := by
    have hm:=congrArg (fun K:Subgroup G=>conjugate K (g:G)) hY
    change (B⊓Q).map (MulAut.conj (g:G)⁻¹).toMonoidHom=
      (A⊓B).map (MulAut.conj (g:G)⁻¹).toMonoidHom at hm
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective,
      map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective] at hm
    change conjugate B (g:G)⊓conjugate Q (g:G)=B⊓conjugate B (g:G) at hm
    rwa [htwice,hQQ,inf_comm B A] at hm
  have hWEA:IsElementaryAbelian 2 W:=hWW.symm ▸ hEA
  have hWi:W.relIndex A=2 := by
    rw [inf_relIndex_left]
    exact (nonabelian_core_indices d h hU hV).1
  have hnA:H≤normalizer (A:Set G):=le_normalizer_conjugateSpanBy V H
  have hnQ:(T:Subgroup G)≤normalizer (Q:Set G):=le_sup_right.trans
    ((L⊔(T:Subgroup G):Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G))))
  have hnW:(T:Subgroup G)≤normalizer (W:Set G):=
    (le_inf (h.T_le_H.trans hnA) hnQ).trans inf_normalizer_le_normalizer_inf
  have hHW:H≤normalizer (W:Set G):=normalizes_elementary_index_two_of_sylow H A W
    (T.subtype h.T_le_H) inf_le_left hWEA hWi (fun he=>hV he.toIsMulCommutative) hnA
    (fun t ht=>hnW ht)
  have hVW:V≤W:=hVE.trans hWW.ge
  have hAW:A≤W:=conjugateSpanBy_le hVW hHW
  have hWA:W=A:=le_antisymm inf_le_left hAW
  exact hV (hWA ▸ hWEA).toIsMulCommutative


/-- The displaced seed has nontrivial image in the actual H/O₂(H) quotient. -/
theorem pair_conjugate_seed_quotient_nontrivial
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let Ug:=conjugate F.UH (g:G)
    Ug≤conjugate F.VH (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2 ∧
      Ug≤H ∧ ¬Ug≤F.QH ∧
      (Ug.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))≠⊥ := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U:=F.UH
  let Ug:=conjugate U (g:G)
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  have hUQ:U≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  have hQQ:conjugate Q (g:G)=Q:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Q:Set G)).inv_mem
      (((L⊔(T:Subgroup G):Subgroup G).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G)))) g.property))
  have hUgQ:Ug≤Q:=(map_mono hUQ).trans hQQ.le
  have hUgH:Ug≤H:=hUgQ.trans ((h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H)
  have hnot:¬Ug≤F.QH := by
    intro hle
    have hEq:F.DHg (g:G)=Ug:=inf_eq_left.mpr hle
    have hm:=congrArg (fun K:Subgroup G=>conjugate K (g:G)) hEq
    have htwice:conjugate Ug (g:G)=U:=h.conjugate_twice_eq_of_square
      (le_normalizer_conjugateSpanBy V₃ H) (h.square_mem_local_of_core_quotient_square g hs)
    rw [(h.intersection_exchange_of_core_quotient_square g hs).2.1,htwice] at hm
    exact (pair_D_lt_seed_span d h hU hV g hs hout).ne hm
  refine ⟨le_inf (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)) hUgQ,hUgH,hnot,?_⟩
  intro hbot
  have hk:Ug.subgroupOf H≤pCore 2 H := by
    have hh:=(Subgroup.map_eq_bot_iff (f:=QuotientGroup.mk' (pCore 2 H)) _).mp hbot
    simpa only [QuotientGroup.ker_mk'] using hh
  apply hnot
  have hm:=map_mono (f:=H.subtype) hk
  rwa [map_subgroupOf_eq_of_le hUgH] at hm

/-- The complete original13.7.11 for the unchanged source choice of g. -/
theorem exists_source_pair_strict_D
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let Ug:=conjugate F.UH (g:G)
      F.DH (g:G)<F.UH ∧
      Ug≤conjugate F.VH (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2 ∧
      Ug≤H ∧ ¬Ug≤F.QH ∧
      (Ug.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))≠⊥ := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_D_lt_seed_span d h hU hV (inclusion le_sup_left g) hs hout,
    pair_conjugate_seed_quotient_nontrivial d h hU hV (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
