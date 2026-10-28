module

public import CFSG.Quasithin.Chapter13.Section07.PairStrictD
public import CFSG.Quasithin.Chapter13.Section07.CoreImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.LineCoreCard

/-!
# The original fixed quotient of index four in13.7.12(1)

The natural point-core image has order eight, while HC has the same
order-two image as VH. The relative-index tower gives the original
denominator (QH intersection Q)HC index four in QH. Normalization and the
proved E-intersection identity place the relevant commutators in HC.

The actual quotient-map consumer constructs HC normal in H and proves
that the original actor and denominator images commute in H/HC. It keeps
the genuine earlier noncentrality on the original point normalizer G1;
no duality, faithful-action or desired index conclusion is assumed.
Source: Aschbacher--Smith13.7.12(1), printed p.942.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup NaturalAction
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem local_core_fixed_index_four
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥) :
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let QH:=H.pCoreIn 2
    let C:=Section08.Source.HC H V₃
    ((QH⊓Q)⊔C).relIndex QH=4 := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let Q:=X.pCoreIn 2
  let QH:=H.pCoreIn 2
  let C:=Section08.Source.HC H V₃
  let K:=QH⊓Q
  have hCQ:C≤QH := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro z hz
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hz.1,fun u hu=>by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hz.2 u hu)]
      exact V₁.one_mem⟩
  have hKQ:K≤QH:=inf_le_left
  have hJQ:K⊔C≤QH:=sup_le hKQ hCQ
  have hKn:QH≤normalizer (K:Set G):=(le_inf QH.le_normalizer
    ((h.QH_le_T.trans le_sup_right).trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))).trans inf_normalizer_le_normalizer_inf
  have hki:K.relIndex QH=8 := by
    rw [inf_relIndex_left,core_relIndex_eq_image_card d h QH h.QH_le_T]
    have him:=core_image_of_point_noncentral d h hU hV hHG hne
    change (QH.subgroupOf X).map (permutation d)=_ at him
    rw [him]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.line_core_card _
      (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
  have hkC:K.relIndex C=2 := by
    have he:(QH⊓Q).subgroupOf C=Q.subgroupOf C := by
      ext z
      exact ⟨fun hz=>hz.2,fun hz=>⟨hCQ z.property,hz⟩⟩
    change ((QH⊓Q).subgroupOf C).index=2
    rw [he]
    exact (nonabelian_core_indices d h hU hV).2
  have hkJ:K.relIndex (K⊔C)=2 := by
    let : (K.subgroupOf QH).Normal:=normal_subgroupOf_of_le_normalizer hKn
    have hi:=relIndex_sup_left (C.subgroupOf QH) (K.subgroupOf QH)
    rw [←subgroupOf_sup hKQ hCQ,relIndex_subgroupOf hJQ,relIndex_subgroupOf hCQ] at hi
    exact hi.trans hkC
  have hm:=relIndex_mul_relIndex K (K⊔C) QH le_sup_left hJQ
  rw [hki,hkJ] at hm
  change (K⊔C).relIndex QH=4
  omega


theorem pair_fixed_core_commutator
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let QH:=H.pCoreIn 2
    let C:=Section08.Source.HC H V₃
    ⁅conjugate (Section08.Source.VH H V) (g:G)⊓Q,(QH⊓Q)⊔C⁆≤C := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let QH:=H.pCoreIn 2
  let C:=Section08.Source.HC H V₃
  let B:=conjugate F.VH (g:G)
  let A:=B⊓Q
  let R:=QH⊓Q
  have hQH:Q≤H:=(h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H
  have hAH:A≤H:=inf_le_right.trans hQH
  have hRH:R≤H:=inf_le_left.trans (pCoreIn_le 2 H)
  have hHC:H≤normalizer (C:Set G):=(le_inf H.le_normalizer
    ((le_normalizer_conjugateSpanBy V₃ H).trans (normalizer_le_normalizer_centralizer F.UH))).trans
      inf_normalizer_le_normalizer_inf
  have hQQ:conjugate Q (g:G)=Q:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Q:Set G)).inv_mem
      (((L⊔(T:Subgroup G):Subgroup G).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G)))) g.property))
  have hQB:Q≤normalizer (B:Set G) := by
    have hn:Q≤normalizer (F.VH:Set G):=hQH.trans (le_normalizer_conjugateSpanBy V H)
    have hm:conjugate Q (g:G)≤normalizer (conjugate F.VH (g:G):Set G):=
      (map_mono hn).trans (le_normalizer_map (H:=F.VH) (MulAut.conj (g:G)⁻¹).toMonoidHom)
    rwa [hQQ] at hm
  have hQA:Q≤normalizer (A:Set G):=(le_inf hQB Q.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hRA:R≤normalizer (A:Set G):=inf_le_right.trans hQA
  have hAQH:A≤normalizer (QH:Set G):=hAH.trans
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=F))
  have hcomm:⁅A,R⁆≤C := by
    have h1:⁅A,R⁆≤A:=le_normalizer_iff_commutator_le_left.mp hRA
    have h2:⁅A,R⁆≤QH:=(commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hAQH)
    have h3:A⊓QH≤F.EHg (g:G):=le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hc: F.EHg (g:G)≤C := by
      obtain ⟨_,he,hEC,_⟩:=pair_E_source_conclusions d h hU hV g hs hout
      exact he.le.trans (hEC.trans inf_le_right)
    exact (le_inf h1 h2).trans (h3.trans hc)
  have hRK:R≤commutatorPreimage H A C:=le_commutatorPreimage hRH
    (by rw [commutator_comm];exact hcomm)
  have hCK:C≤commutatorPreimage H A C:=le_commutatorPreimage inf_le_left
    (le_normalizer_iff_commutator_le_left.mp (hAH.trans hHC))
  rw [commutator_comm]
  exact (commutator_mono (sup_le hRK hCK) le_rfl).trans
    (commutator_commutatorPreimage_le H A C hHC)

/-- Literal quotient-map centralization in13.7.12(1), with the original denominator index. -/
theorem pair_fixed_core_quotient
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let QH:=H.pCoreIn 2
    let C:=Section08.Source.HC H V₃
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    let R:=(QH⊓Q)⊔C
    ∃hc:(C.subgroupOf H).Normal, letI:=hc;
      let q:=QuotientGroup.mk' (C.subgroupOf H)
      ⁅(A.subgroupOf H).map q,(R.subgroupOf H).map q⁆=⊥ ∧ R.relIndex QH=4 := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let C:=Section08.Source.HC H V₃
  let A:=conjugate F.VH (g:G)⊓Q
  let R:=(H.pCoreIn 2⊓Q)⊔C
  have hn:H≤normalizer (C:Set G):=(le_inf H.le_normalizer
    ((le_normalizer_conjugateSpanBy V₃ H).trans (normalizer_le_normalizer_centralizer F.UH))).trans
      inf_normalizer_le_normalizer_inf
  let hc:(C.subgroupOf H).Normal:=normal_subgroupOf_of_le_normalizer hn
  refine ⟨hc,?_,local_core_fixed_index_four d h hU hV hHG hne⟩
  let q:=QuotientGroup.mk' (C.subgroupOf H)
  change ⁅(A.subgroupOf H).map q,(R.subgroupOf H).map q⁆=⊥
  rw [←map_commutator]
  apply (Subgroup.map_eq_bot_iff (f:=q) _).mpr
  rw [QuotientGroup.ker_mk']
  apply commutator_le.mpr
  intro a ha r hr
  exact pair_fixed_core_commutator d h hU hV g hs hout (commutator_mem_commutator ha hr)

/-- The original chosen pair supplies both the nontrivial offender candidate
and the exact quotient of index four centralized by its containing core factor. -/
theorem exists_source_pair_fixed_core
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let C:=Section08.Source.HC H V₃
      let A:=conjugate F.VH (g:G)⊓Q
      let R:=(H.pCoreIn 2⊓Q)⊔C
      F.DH (g:G)<F.UH ∧
      ∃hc:(C.subgroupOf H).Normal, letI:=hc;
        let q:=QuotientGroup.mk' (C.subgroupOf H)
        ⁅(A.subgroupOf H).map q,(R.subgroupOf H).map q⁆=⊥ ∧ R.relIndex (H.pCoreIn 2)=4 := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_D_lt_seed_span d h hU hV (inclusion le_sup_left g) hs hout,
    pair_fixed_core_quotient d h hU hV hHG hne (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
