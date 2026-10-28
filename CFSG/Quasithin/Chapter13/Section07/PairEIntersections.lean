module

public import CFSG.Quasithin.Chapter13.Section07.PairSeedSpan
public import CFSG.Quasithin.Chapter13.Section07.SeedCommutator

/-!
# The original E-intersections equal ZI

Natural orthogonality and normal closure give [VH,QH] <= UH without
requiring the earlier noncentrality used for equality. The actual
commutator preimage places EHg inside UH^g ZI; the proved DHg containment
then forces EHg = ZI. The source square condition gives EH = ZI too.

The final consumer constructs the original nonorthogonal g and returns
both literal identities of13.7.10(4) and all conclusions of(7). Only the
original F.9 applicability, abelian seed span and contrary nonabelian full
span remain inputs; full13.7.4 faithfulness is not assumed here.
Source: Aschbacher--Smith13.7.10(4),(7), printed pp.941--942.
-/

public section

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The bound in13.7.3(6) needs only natural orthogonality, before its equality case. -/
theorem source_span_core_commutator_le
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ⁅Section08.Source.VH H V,H.pCoreIn 2⁆≤Section08.Source.UH H V₃ := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hHU:H≤normalizer (F.UH:Set G):=le_normalizer_conjugateSpanBy V₃ H
  have hHQ:H≤normalizer (F.QH:Set G):=ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=F)
  have hs:⁅V,F.QH⁆≤V₃:=commutator_le_seed_of_centralizes_line d F.QH
    (h.QH_le_T.trans le_sup_right) ((pCoreIn_le 2 H).trans h.H_centralizes)
  have hV:V≤commutatorPreimage H F.QH F.UH:=
    le_commutatorPreimage h.V_le_H (hs.trans (le_conjugateSpanBy V₃ H))
  have hspan:F.VH≤commutatorPreimage H F.QH F.UH:=
    conjugateSpanBy_le hV (commutatorPreimage_normalized _ _ _ _ hHU H.le_normalizer hHQ hHU)
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hHU)

theorem pair_Eg_eq_intersection
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).EHg (g:G)=
      Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G) := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let A:=F.VH
  let B:=conjugate A (g:G)
  let U:=F.UH
  let Ug:=conjugate U (g:G)
  let I:=A⊔B
  let E:=A⊓B
  have hEQ:E≤F.QH:=inf_le_left.trans (VH_le_core d h hU)
  have hUA:U≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUgB:Ug≤B:=map_mono hUA
  have hUgI:Ug≤I:=hUgB.trans le_sup_right
  have hnE:I≤normalizer (E:Set G):=(pair_intersection_layer d h hU g hout).2.2.1
  have hprod:((Ug⊔E:Subgroup G):Set G)=(Ug:Set G)*(E:Set G):=
    coe_mul_of_left_le_normalizer_right Ug E (hUgI.trans hnE)
  have hDg:F.DHg (g:G)≤E:=(pair_D_spans_le_intersection d h hU hV g hs hout).2.1
  have hcomm:⁅A,F.QH⁆≤U:=source_span_core_commutator_le d h
  apply le_antisymm
  · intro z hz
    have hzU:z∈Ug⊔E:=(pair_commutator_preimage d h hU hV g hout z hz.1).mp
      (fun a ha=>mem_sup_left (hcomm (commutator_mem_commutator ha hz.2)))
    have hzm:z∈(Ug:Set G)*(E:Set G):=hprod ▸ hzU
    obtain ⟨u,hu,e,he,hue⟩:=hzm
    have huQ:u∈F.QH := by
      have hm:=F.QH.mul_mem hz.2 (F.QH.inv_mem (hEQ he))
      rw [←hue,mul_inv_cancel_right] at hm
      exact hm
    have huE:u∈E:=hDg ⟨hu,huQ⟩
    exact hue ▸ E.mul_mem huE he
  · exact le_inf inf_le_right hEQ

theorem pair_E_intersections
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let E:=F.VH⊓conjugate F.VH (g:G)
    F.EH (g:G)=E ∧ F.EHg (g:G)=E := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let A:=F.VH
  let B:=conjugate A (g:G)
  let E:=A⊓B
  have heg:F.EHg (g:G)=E:=pair_Eg_eq_intersection d h hU hV g hs hout
  have htwice:conjugate B (g:G)=A:=h.conjugate_twice_eq_of_square
    (le_normalizer_conjugateSpanBy V H) (h.square_mem_local_of_core_quotient_square g hs)
  have hee:conjugate E (g:G)=E := by
    change (A⊓B).map (MulAut.conj (g:G)⁻¹).toMonoidHom=E
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective]
    change B⊓conjugate B (g:G)=A⊓B
    rw [htwice,inf_comm]
  have hm:=congrArg (fun K:Subgroup G=>conjugate K (g:G)) heg
  rw [(h.intersection_exchange_of_core_quotient_square g hs).2.2.2,hee] at hm
  exact ⟨hm,heg⟩

/-- All original intersection conclusions in13.7.10(7), without a faithful-action input. -/
theorem pair_E_source_conclusions
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let E:=F.VH⊓conjugate F.VH (g:G)
    F.EH (g:G)=E ∧ F.EHg (g:G)=E ∧
      E≤(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2⊓Section08.Source.HC H V₃ ∧
      ⁅F.EHg (g:G),F.VH⁆≤V₁ := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let E:=F.VH⊓conjugate F.VH (g:G)
  obtain ⟨he,heg⟩:=pair_E_intersections d h hU hV g hs hout
  refine ⟨he,heg,?_,?_⟩
  · have hES:E≤(F.VH⊔conjugate F.VH (g:G):Subgroup G).pCoreIn 2:=
      (pair_intersection_layer d h hU g hout).2.1
    have hEQ:=hES.trans ((pair_twoCore_quotient d h hU hV g hout).1.le.trans inf_le_right)
    exact le_inf hEQ (inf_le_left.trans (VH_centralizes_UH d h hU))
  · rw [heg]
    exact (commutator_mono inf_le_left le_rfl).trans (commutator_VH_le_point d h hU)

/-- The original13.7.10(4),(7) for a constructed nonorthogonal source conjugator.
The earlier abelian seed span and F.9 applicability remain the original inputs. -/
theorem exists_source_pair_span_intersections
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let B:=conjugate F.VH (g:G)
      let E:=F.VH⊓B
      ((conjugateSpanBy F.UH (F.VH⊔B)⊔E:Subgroup G):Set G)=
        (F.UH:Set G)*(conjugate F.UH (g:G):Set G)*(E:Set G) ∧
      (∀z∈B,(∀a∈F.VH,⁅a,z⁆∈F.UH⊔E) ↔ z∈conjugate F.UH (g:G)⊔E) ∧
      F.EH (g:G)=E ∧ F.EHg (g:G)=E ∧
      E≤(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2⊓Section08.Source.HC H V₃ ∧
      ⁅F.EHg (g:G),F.VH⁆≤V₁ := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,
    pair_seed_span_product d h hU hV (inclusion le_sup_left g) hs hout,
    pair_commutator_preimage d h hU hV (inclusion le_sup_left g) hout,
    pair_E_source_conclusions d h hU hV (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
