module

public import CFSG.Quasithin.Chapter13.Section07.PairOffenderIndices
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryConjugationSection.OffenderIndex

/-!
# The original offenders on the seed quotient

F.9 identifies the kernel of the literal H-action on UH/V1 with O2(H).
The original two candidates therefore act on this faithful quotient
representation; their fixed-index bounds prove both offender inequalities.
The final consumer constructs the original conjugator and best offenders
inside each candidate. This proves the UH/V1 part of13.7.12(3). The
separate faithfulness claim for UH/U0 is not used or asserted here.
Source: Aschbacher--Smith13.7.12(3) and B.1.4(4), printed p.942.
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
/-- The actual faithful H/O₂(H)-action on UH/V₁ and both original offenders. -/
theorem source_tilde_offenders
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let U:=Section08.Source.UH H V₃
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
    let Ug:=conjugate U (g:G)
    let π:=QuotientGroup.mk' (pCore 2 H)
    ∃hE:IsElementaryAbelian 2 U, letI:=hE;
      ∃ (σ:Representation (ZMod 2) (H⧸pCore 2 H) (Additive (U⧸V₁.subgroupOf U)))
        (c:Representation.BinaryConjugationSection H U V₁ (σ.comp π)),
        Function.Injective σ ∧
        (∀u:U,(c.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
        IsOffender σ ((A.subgroupOf H).map π) ∧
        IsOffender σ ((Ug.subgroupOf H).map π) := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U:=F.UH
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let A:=conjugate F.VH (g:G)⊓Q
  let Ug:=conjugate U (g:G)
  let π:=QuotientGroup.mk' (pCore 2 H)
  have hE:IsElementaryAbelian 2 U:=h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy V H).trans (VH_le_core d h hU))
  let :=hE
  have hZ:V₁≤U:=h.point_lt.le.trans (le_conjugateSpanBy V₃ H)
  have hZH:V₁≤centralizer (H:Set G):=le_centralizer_iff.mp h.H_centralizes
  have hk:∀a:H,π a=1 ↔ ∀u∈U,⁅(a:G),u⁆∈V₁ := by
    intro a
    have ha:π a=1 ↔ (a:G)∈F.QH := by
      change QuotientGroup.mk' (pCore 2 H) a=1 ↔ (a:G)∈F.QH
      constructor
      · intro hq
        exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (N:=pCore 2 H) a).mp hq)
      · rintro ⟨b,hb,he⟩
        exact (QuotientGroup.eq_one_iff (N:=pCore 2 H) a).mpr ((Subtype.ext he : b=a) ▸ hb)
    rw [ha,←h.kernel_UH_eq_QH,h.mem_kernel_iff h.UH_le_H]
    constructor
    · intro hc u hu
      rw [←commutatorElement_inv]
      exact V₁.inv_mem (hc.2 u hu)
    · intro hc
      refine ⟨a.property,?_⟩
      intro u hu
      rw [←commutatorElement_inv]
      exact V₁.inv_mem (hc u hu)
  obtain ⟨σ,c,hinj,hcoord⟩:=Representation.BinaryConjugationSection.exists_faithful_quotient_actor
    H U V₁ h.UH_le_H hZ (le_normalizer_conjugateSpanBy V₃ H)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) π (QuotientGroup.mk'_surjective _) hk
  have hcard (B:Subgroup G) (hBH:B≤H) : Nat.card ((B.subgroupOf H).map π)=F.QH.relIndex B := by
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
  have apply_bound (B:Subgroup G) (hBH:B≤H) (he:IsElementaryTwo ((B.subgroupOf H).map π))
      (hi:(U⊓centralizer (B:Set G)).relIndex U≤F.QH.relIndex B) : IsOffender σ ((B.subgroupOf H).map π) := by
    apply c.offender_of_fixed_index σ π B (U⊓centralizer (B:Set G)) inf_le_left
      (le_inf hZ (hZH.trans (centralizer_le hBH)))
    · rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    · exact he
    · rwa [hcard B hBH]
  exact ⟨hE,σ,c,hinj,hcoord,apply_bound A hAH ⟨hAne,hEA⟩ hiA,
    apply_bound Ug hUgH ⟨hUgne,hUgEA⟩ hiUg⟩


/-- Original13.7.12(3) on UH/V₁, including best offenders inside both literal candidates. -/
theorem exists_source_tilde_FF
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let U:=Section08.Source.UH H V₃
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let A:=conjugate (Section08.Source.VH H V) (g:G)⊓Q
      let Ug:=conjugate U (g:G)
      let π:=QuotientGroup.mk' (pCore 2 H)
      ∃hE:IsElementaryAbelian 2 U, letI:=hE;
        ∃ (σ:Representation (ZMod 2) (H⧸pCore 2 H) (Additive (U⧸V₁.subgroupOf U)))
          (c:Representation.BinaryConjugationSection H U V₁ (σ.comp π)),
          Function.Injective σ ∧
          (∀u:U,(c.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
          IsFFModule σ ∧
          (∃B≤(A.subgroupOf H).map π,IsBestOffender σ B) ∧
          (∃B≤(Ug.subgroupOf H).map π,IsBestOffender σ B) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  obtain ⟨hE,σ,c,hinj,hcoord,hA,hUg⟩:=source_tilde_offenders d h hU hV (inclusion le_sup_left g) hs hout
  exact ⟨g,hs,hspan,hout,hE,σ,c,hinj,hcoord,⟨_,hA⟩,
    hA.exists_bestOffender σ,hUg.exists_bestOffender σ⟩

end CFSG.Quasithin.Chapter13.Section07
