module
public import CFSG.Quasithin.Chapter4.Section01.ResidualSylow
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.SylowKernelCore
import Mathlib.Tactic
/-!
# Radicality and core bounds in the actual outside overgroup

The residual's maximal signalizer controls the two-core of its relative
normalizer. Characteristic-normalizer containment therefore makes the
original R radical inside H. The radical core theorem gives both inclusions
O2(H) <= O2(H intersect M) <= R. Relative normalizers and their images are
transported literally through subgroup inclusions.
Source: Aschbacher--Smith,4.1.4(5), printed p.607.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A normal two-perfect actor's maximal signalizer is radical in any
overgroup whose relative normalizer stays in the specified local subgroup. -/
theorem relative_normalizer_core_of_sylow_sectionCentralizer {Y A H R : Subgroup G}
    (hAH : A ≤ H) (hYA : Y ≤ A) (hYN : (Y.subgroupOf A).Normal)
    (hY : IsPPerfect 2 Y)
    (hS : ∃ S : Sylow 2 (sectionCentralizerIn A Y),
      (S : Subgroup (sectionCentralizerIn A Y)).map
        (sectionCentralizerIn A Y).subtype = R)
    (hNA : H ⊓ normalizer (R : Set G) ≤ A) :
    (H ⊓ normalizer (R : Set G)).pCoreIn 2 = R := by
  have hs : ∃ S : Sylow 2 (ChapterA.Section04.twoSectionCentralizer Y A),
      (S : Subgroup (ChapterA.Section04.twoSectionCentralizer Y A)).map
        (ChapterA.Section04.twoSectionCentralizer Y A).subtype = R := by
    rwa [← sectionCentralizerIn_eq_twoSectionCentralizer]
  have hm := (ChapterA.Section04.isMaximalTwoSignalizer_iff Y A R).mp
    ((ChapterA.Section04.maximal_signalizer_iff_sylow Y A R hYA hYN.isSubnormal hY).mpr hs)
  have hRN : R ≤ H ⊓ normalizer (R : Set G) :=
    le_inf (hm.1.le.trans hAH) R.le_normalizer
  have hRQ : R ≤ (H ⊓ normalizer (R : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hm.1.isPGroup hRN inf_le_right
  have hYR : Y ≤ H ⊓ normalizer (R : Set G) :=
    le_inf (hYA.trans hAH) hm.1.normalizes
  apply le_antisymm ?_ hRQ
  apply hm.2 _ ((ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr ?_) hRQ
  exact ⟨(pCoreIn_le 2 _).trans hNA,isPGroup_pCoreIn 2 _,
    hYR.trans ((H ⊓ normalizer (R : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))⟩

omit [Finite G] in
/-- Map the relative normalizer core back into H without replacing any
normalizer or prime core by an abstract isomorphic subgroup. -/
theorem relative_radical_of_normalizer_core {R H : Subgroup G} (hRH : R ≤ H)
    (hne : R ≠ ⊥) (hc : (H ⊓ normalizer (R : Set G)).pCoreIn 2 = R) :
    IsPRadical 2 (R.subgroupOf H) := by
  have hn : (normalizer (R.subgroupOf H : Set H)).map H.subtype =
      H ⊓ normalizer (R : Set G) := by
    rw [← subgroupOf_normalizer_eq hRH,subgroupOf_map_subtype,inf_comm]
  refine ⟨?_,?_⟩
  · intro he
    apply hne
    have he' := congrArg (fun Q : Subgroup H => Q.map H.subtype) he
    simpa only [map_subgroupOf_eq_of_le hRH,Subgroup.map_bot] using he'
  · change (normalizer (R.subgroupOf H : Set H)).pCoreIn 2 = R.subgroupOf H
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,hn,hc,
      map_subgroupOf_eq_of_le hRH]

/-- The ambient core containment attached to a literal relative radical. -/
theorem core_le_of_relative_radical {R H : Subgroup G}
    (hr : IsPRadical 2 (R.subgroupOf H)) : H.pCoreIn 2 ≤ R := by
  have h := pCore_le_of_pCore_normalizer_le (R.subgroupOf H) hr.isPGroup hr.2.le
  rintro x ⟨y,hy,rfl⟩
  exact h hy

/-- Full4.1.4(5): radicality in H and both source core bounds. -/
theorem lemma_4_1_4_5 {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus)
    (hH : H ∈ Chapter1.H G) (hIH : I ≤ H) (hout : ¬ H ≤ M) :
    (H ⊓ normalizer (I.pCoreIn 2 : Set G)).pCoreIn 2 = I.pCoreIn 2 ∧
      IsPRadical 2 ((I.pCoreIn 2).subgroupOf H) ∧
      H.pCoreIn 2 ≤ (H ⊓ M).pCoreIn 2 ∧ (H ⊓ M).pCoreIn 2 ≤ I.pCoreIn 2 := by
  let R := I.pCoreIn 2
  let A := H ⊓ M
  have hRH : R ≤ H := (pCoreIn_le 2 I).trans hIH
  have hRM : R ≤ M := (pCoreIn_le 2 I).trans (hI.1.1.1.trans hminus.1)
  have hRA : R ≤ A := le_inf hRH hRM
  have hn : normalizer (R : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self _ hI.1.1.2.2.2).trans
      (lemma_4_1_4_2 hyp hminus hI)
  obtain ⟨_,hY,hYN⟩ := lemma_4_1_4_3 hyp hI.1.1 hIH
  have hS := (lemma_4_1_4_4 hyp hminus hI hH hIH hout).1
  have hc := relative_normalizer_core_of_sylow_sectionCentralizer inf_le_left hY hYN
    (isPPerfect_embedded_pResidual 2 (X ⊓ H)) hS (le_inf inf_le_left (inf_le_right.trans hn))
  have hr := relative_radical_of_normalizer_core hRH hI.1.1.2.2.2 hc
  have he : A ⊓ normalizer (R : Set G) = H ⊓ normalizer (R : Set G) := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    exact le_inf (le_inf inf_le_left (inf_le_right.trans hn)) inf_le_right
  have hrA := relative_radical_of_normalizer_core hRA hI.1.1.2.2.2 (he ▸ hc)
  have hHcore : H.pCoreIn 2 ≤ A := (core_le_of_relative_radical hr).trans hRA
  have hcores : H.pCoreIn 2 ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hHcore
      (inf_le_left.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  exact ⟨hc,hr,hcores,core_le_of_relative_radical hrA⟩
end CFSG.Quasithin.Chapter4
