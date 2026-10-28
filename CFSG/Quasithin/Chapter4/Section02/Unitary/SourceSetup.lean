module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FullModule
public import CFSG.Quasithin.Chapter4.Section02.Unitary.ComponentCover
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
import Mathlib.Tactic
/-!
# The actual C.2.8 setup in the normalized Fundamental Setup

The original maximal counterexample produces the normal residual in H∩N(L).
The source clauses of 4.1.4 give its component, Sylow and characteristic
normalizer conditions; 4.1.5 supplies the full omega-center module and its
normalizer bound. The chosen nonzero module proves this full module nonzero.
All subgroups, quotient actions and embeddings remain the original ones.

Source: Aschbacher–Smith, 4.2.4 and Hypothesis C.2.8, printed pp.608–609,147.
-/
public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_join_eq_of_sectionSylow {Y A R : Subgroup G}
    (hYA : Y ≤ A) (hYN : (Y.subgroupOf A).Normal) (hY : IsPPerfect 2 Y)
    (hS : ∃ S : Sylow 2 (sectionCentralizerIn A Y),
      (S : Subgroup (sectionCentralizerIn A Y)).map (sectionCentralizerIn A Y).subtype = R) :
    (Y ⊔ R).pCoreIn 2 = R := by
  have hs : ∃ S : Sylow 2 (ChapterA.Section04.twoSectionCentralizer Y A),
      (S : Subgroup (ChapterA.Section04.twoSectionCentralizer Y A)).map
        (ChapterA.Section04.twoSectionCentralizer Y A).subtype = R := by
    rwa [← sectionCentralizerIn_eq_twoSectionCentralizer]
  have hm := (ChapterA.Section04.isMaximalTwoSignalizer_iff _ _ _).mp
    ((ChapterA.Section04.maximal_signalizer_iff_sylow Y A R hYA hYN.isSubnormal hY).mpr hs)
  have hRA : R ≤ (Y ⊔ R).pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup le_sup_right
    (sup_le hm.1.normalizes R.le_normalizer)
  refine le_antisymm (hm.2 _ ((ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr ?_) hRA) hRA
  exact ⟨(pCoreIn_le 2 _).trans (sup_le hYA hm.1.le),isPGroup_pCoreIn 2 _,
    le_sup_left.trans ((Y ⊔ R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))⟩

/-- The original normalized source constructs every clause of C.2.8 on
its actual outside H, residual LH, core R and full omega-center commutator.
No local classifier or C.2.8 certificate is an input. -/
theorem source_C28_of_muStar {K : GroupClass} {T : Sylow 2 G}
    {L V Mminus J H : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hminus : Mminus ∈ sigma (normalizer (L : Set G)) L)
    (hJ : J ∈ muStar (normalizer (L : Set G)) L Mminus)
    (hH : IsMaximalTwoLocal H) (hJH : J ≤ H) (hout : ¬ H ≤ normalizer (L : Set G))
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRS : J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    ChapterC.HypothesisC28 K H (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
      (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) := by
  let N := normalizer (L : Set G)
  let A := H ⊓ N
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let Q := (S : Subgroup (sectionCentralizerIn N L)).map (sectionCentralizerIn N L).subtype
  let W := fullModule L Q
  have hyp := source_hypothesis411 h hM
  have hmem := Chapter1.mem_H_of_isTwoLocal hH.1
  have hr := Chapter4.Section04.chosen_intersection_twoResidual_eq_solvableResidual h hJ.1.1.2.2.1 hJH
  obtain ⟨hcover,hYA,hYN⟩ := lemma_4_1_4_3 hyp hJ.1.1 hJH
  rw [hr] at hcover hYA hYN
  have hpY : IsPPerfect 2 Y := by
    change IsPPerfect 2 ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
    rw [← hr]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ H)
  have hSY := (lemma_4_1_4_4 hyp hminus hJ hmem hJH hout).1
  rw [hr] at hSY
  have hdata := fullModule_data hyp.plus_perfect
    (sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S)
  have hWne := fullModule_ne_bot_of_chosen h D hM S
  have hWcenter := lemma_4_1_5_1 hyp hminus hJ S hRS hdata.1
  have hWY := lemma_4_1_5_3 hyp hJ.1.1 hJH S hdata.1 hdata.2.2
  rw [hr] at hWY
  have hRA : R ≤ A := (pCoreIn_le 2 J).trans
    (le_inf hJH (hJ.1.1.1.trans hminus.1))
  have hWA : W ≤ A := hWcenter.trans ((map_subtype_le _).trans hRA)
  have hWleY : W ≤ Y := by
    change W = ⁅W,Y⁆ at hWY
    rw [hWY]
    exact le_normalizer_iff_commutator_le_right.mp
      (hWA.trans ((normal_subgroupOf_iff_le_normalizer hYA).mp hYN))
  have hspan : conjugateSpanBy Y A = Y := le_antisymm
    (conjugateSpanBy_le le_rfl ((normal_subgroupOf_iff_le_normalizer hYA).mp hYN))
    (le_conjugateSpanBy Y A)
  have hcore := core_join_eq_of_sectionSylow hYA hYN hpY hSY
  have hNV := lemma_4_1_5_2 hyp S hWne hdata.1 rfl
  refine
    { sqtk := h.simpleQTKE.twoLocal_sqtk hH.1
      radical_isTwoGroup := isPGroup_pCoreIn 2 J
      radical_le := hRA
      local_le := inf_le_left
      local_fitting := lemma_4_1_4_6 hyp hminus hJ hmem hJH hout
      core_nontrivial := hmem
      component_le := hYA
      component := source_intersection_isCComponent h hM hJ.1.1.2.2.1 hJH
      section_sylow := ?_
      characteristic_control := ?_
      module_nontrivial := hWne
      module_elementary := hdata.2.1
      module_le := ?_
      module_commutator := ?_
      module_central := ?_
      module_normalizer := le_inf inf_le_left (inf_le_right.trans hNV) }
  · change ∃ S' : Sylow 2 (ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy Y A) A), _
    rw [hspan,← sectionCentralizerIn_eq_twoSectionCentralizer]
    exact hSY
  · have hc := characteristicNormalizerClosure_subgroupOf_le (hRA.trans inf_le_left)
      (lemma_4_1_4_2 hyp hminus hJ)
    intro x hx
    exact ⟨x.property,hc hx⟩
  · change W ≤ conjugateSpanBy Y A
    rwa [hspan]
  · change W = ⁅W,conjugateSpanBy Y A⁆
    rwa [hspan]
  · change W ≤ (center ((conjugateSpanBy Y A ⊔ R).pCoreIn 2)).map _
    rw [hspan,hcore]
    exact hWcenter
end CFSG.Quasithin.Chapter4.Section02.Unitary
