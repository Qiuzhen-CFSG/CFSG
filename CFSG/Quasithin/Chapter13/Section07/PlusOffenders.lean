module

public import CFSG.Quasithin.Chapter13.Section07.PairOffenderIndices
public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex
public import Theory.Representation.Quotient
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Original plus-module offender inequalities

The central duality source constructs the literal UH/U0 action, and its
kernel contains O₂(H), so it descends to H/O₂(H). The same fixed-index
calculation proves both original candidates are offenders for this actual
plus action. This theorem intentionally does not assert faithfulness: that
is the separate source conclusion13.7.4(1).
Source: Aschbacher--Smith13.7.4(1) setup and13.7.12(3), pp.936,942.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The actual plus action and both original offender inequalities, retaining the source duality.
Faithfulness is the separate source conclusion13.7.4(1). -/
theorem source_plus_offenders
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let QH:=H.pCoreIn 2
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let U₀:=U⊓centralizer (QH:Set G)
    let HC:=Section08.Source.HC H V₃
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    let Ug:=conjugate U (g:G)
    let π:=QuotientGroup.mk' (pCore 2 H)
    ∃hE:IsElementaryAbelian 2 U, letI:=hE;
      ∃ (σ:Representation (ZMod 2) (H⧸pCore 2 H) (Additive (U⧸U₀.subgroupOf U)))
        (sU:Representation.BinaryConjugationSection H U U₀ (σ.comp π))
        (sQ:Representation.BinaryConjugationSection H QH HC (Representation.dual (σ.comp π))),
        (∀(q:QH)(u:U),(sQ.coordinates q).toAdd (sU.coordinates u).toAdd=0 ↔ ⁅(q:G),(u:G)⁆=1) ∧
        (∀u:U,(sU.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) ∧
        IsOffender σ ((A.subgroupOf H).map π) ∧
        IsOffender σ ((Ug.subgroupOf H).map π) := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U:=F.UH
  let QH:=F.QH
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let U₀:=U⊓centralizer (QH:Set G)
  let A:=conjugate F.VH (g:G)⊓Q
  let Ug:=conjugate U (g:G)
  let π:=QuotientGroup.mk' (pCore 2 H)
  obtain ⟨hE,ρ,sU,sQ,hpair,hcoord⟩:=source_central_duality d h hU
  let : IsElementaryAbelian 2 U := hE
  have hZ:V₁≤U₀:=le_inf (h.point_lt.le.trans (le_conjugateSpanBy V₃ H))
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes))
  have hQU:⁅QH,U⁆≤U₀:= (commutator_comm QH U).le.trans (h.commutator_UH_QH_le_point.trans hZ)
  have hk:pCore 2 H≤ρ.ker := by
    intro a ha
    apply LinearMap.ext
    intro w
    obtain ⟨u,hu⟩:=sU.onto (Multiplicative.ofAdd w)
    have hw:(sU.coordinates u).toAdd=w:=congrArg Multiplicative.toAdd hu
    change ρ a w=w
    rw [←hw]
    exact sU.fixed_on_imageSpace_of_commutator_le QH U hQU a (mem_map_of_mem H.subtype ha) _
      ((sU.mem_imageSpace_iff U _).mpr ⟨u,u.property,rfl⟩)
  let σ:Representation (ZMod 2) (H⧸pCore 2 H) (Additive (U⧸U₀.subgroupOf U)):=
    Representation.quotientOfLEKer ρ (pCore 2 H) hk
  have hcomp:(σ.comp π)=ρ:=Representation.quotientOfLEKer_comp ρ (pCore 2 H) hk
  have hcard (B:Subgroup G) (hBH:B≤H):Nat.card ((B.subgroupOf H).map π)=QH.relIndex B := by
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have he:=relIndex_map_map_of_injective (pCore 2 H) (B.subgroupOf H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hBH] at he
    exact he.symm
  obtain ⟨hAH,hEA,hAne⟩:=pair_actor_elementary_nontrivial d h hU hV g hs hout
  obtain ⟨hUgA,hUgH,_,hUgne⟩:=pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hUgEA:IsElementaryAbelian 2 ((Ug.subgroupOf H).map π) := by
    let :IsElementaryAbelian 2 ((A.subgroupOf H).map π):=hEA
    have hle:(Ug.subgroupOf H).map π≤(A.subgroupOf H).map π:=map_mono (comap_mono hUgA)
    exact IsElementaryAbelian.of_le hle
  obtain ⟨hiA,hiUg,_⟩:=pair_seed_fixed_index_bounds d h hU hV g hs hout
  have bound (B:Subgroup G) (hBH:B≤H) (he:IsElementaryTwo ((B.subgroupOf H).map π))
      (hi:(U⊓centralizer (B:Set G)).relIndex U≤QH.relIndex B):IsOffender σ ((B.subgroupOf H).map π) := by
    apply Representation.BinaryConjugationSection.offender_of_section_index σ π sU B (U⊓centralizer (B:Set G))
    · rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr (show U⊓centralizer (B:Set G)≤centralizer (B:Set G) from inf_le_right)]
      exact bot_le
    · exact he
    · rwa [hcard B hBH]
  exact ⟨hE,σ,sU,sQ,hpair,hcoord,bound A hAH ⟨hAne,hEA⟩ hiA,bound Ug hUgH ⟨hUgne,hUgEA⟩ hiUg⟩


/-- Construct the original g, plus action, duality and actual best offenders.
The earlier faithful-action conclusion is kept separate. -/
theorem exists_source_plus_FF
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let U:=Section08.Source.UH H V₃
      let QH:=H.pCoreIn 2
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let U₀:=U⊓centralizer (QH:Set G)
      let HC:=Section08.Source.HC H V₃
      let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
      let Ug:=conjugate U (g:G)
      let π:=QuotientGroup.mk' (pCore 2 H)
      ∃hE:IsElementaryAbelian 2 U, letI:=hE;
        ∃ (σ:Representation (ZMod 2) (H⧸pCore 2 H) (Additive (U⧸U₀.subgroupOf U)))
          (sU:Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (sQ:Representation.BinaryConjugationSection H QH HC (Representation.dual (σ.comp π))),
          (∀(q:QH)(u:U),(sQ.coordinates q).toAdd (sU.coordinates u).toAdd=0 ↔ ⁅(q:G),(u:G)⁆=1) ∧
          (∀u:U,(sU.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) ∧
          IsFFModule σ ∧
          (∃B≤(A.subgroupOf H).map π,IsBestOffender σ B) ∧
          (∃B≤(Ug.subgroupOf H).map π,IsBestOffender σ B) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  obtain ⟨hE,σ,sU,sQ,hpair,hcoord,hA,hUg⟩:=source_plus_offenders d h hU hV (inclusion le_sup_left g) hs hout
  exact ⟨g,hs,hspan,hout,hE,σ,sU,sQ,hpair,hcoord,⟨_,hA⟩,
    hA.exists_bestOffender σ,hUg.exists_bestOffender σ⟩

end CFSG.Quasithin.Chapter13.Section07
