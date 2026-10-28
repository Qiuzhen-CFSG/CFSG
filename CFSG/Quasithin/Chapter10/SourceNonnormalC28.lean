module
public import CFSG.Quasithin.Chapter10.SourceNonnormalPushingSetup
public import CFSG.Quasithin.Chapter10.SourceNonnormalIntersectionOrbit
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses

/-!
# C.2.8 for an original nonnormal component orbit

The actual maximal pushing-up counterexample has a component residual
LH=(L∩H)^∞ in H∩M. Its conjugate span is O²(L₀∩H), so the established
4.1.4–5 results apply to that span and to the full omega-center module.
This constructs every clause of C.2.8 with the literal source subgroups,
without requiring L or LH to be normal in M or H∩M.

Source: Aschbacher–Smith, 4.2.4 and 4.2.12, combined manuscript of
1 March 2004, printed pp.608–611. The later C.4.8 normality conclusion
remains a separate source classification theorem.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

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

/-- The genuine orbit-covering counterexample supplies every C.2.8 clause. -/
theorem source_nonnormal_C28_of_muStar
    {Mminus I H : Subgroup G}
    (hminus : Mminus ∈ sigma D.maximalLocal (localOrbit T L))
    (hI : I ∈ muStar D.maximalLocal (localOrbit T L) Mminus)
    (hH : IsMaximalTwoLocal H) (hIH : I ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (horbit : componentOrbit L I = localOrbit T L)
    (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L)))
    (hRS : I.pCoreIn 2 ≤
      (S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
        (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (I.pCoreIn 2)
      (fullModule (localOrbit T L)
        ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
          (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) := by
  let M := D.maximalLocal
  let X := localOrbit T L
  let A := H ⊓ M
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Y := (pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype
  let R := I.pCoreIn 2
  let Q := (S : Subgroup (sectionCentralizerIn M X)).map (sectionCentralizerIn M X).subtype
  let W := fullModule X Q
  have hyp := source_orbit_hypothesis411 D
  have hmem := Chapter1.mem_H_of_isTwoLocal hH.1
  have hIM : I ≤ M := hI.1.1.1.trans hminus.1
  have hLHA : LH ≤ A := le_inf ((map_subtype_le _).trans inf_le_right)
    ((map_subtype_le _).trans (inf_le_left.trans ((le_componentOrbit L T).trans X.le_normalizer)))
  obtain ⟨hcover,hYA,hYN⟩ := lemma_4_1_4_3 hyp hI.1.1 hIH
  have hpY : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 (X ⊓ H)
  have hSY := (lemma_4_1_4_4 hyp hminus hI hmem hIH hout).1
  have hdata := fullModule_data hyp.plus_perfect
    (sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S)
  have hWne := source_orbit_fullModule_ne_bot D S
  have hWcenter := lemma_4_1_5_1 hyp hminus hI S hRS hdata.1
  have hWY := lemma_4_1_5_3 hyp hI.1.1 hIH S hdata.1 hdata.2.2
  have hRA : R ≤ A := (pCoreIn_le 2 I).trans (le_inf hIH hIM)
  have hWA : W ≤ A := hWcenter.trans ((map_subtype_le _).trans hRA)
  have hWleY : W ≤ Y := by
    change W = ⁅W,Y⁆ at hWY
    rw [hWY]
    exact le_normalizer_iff_commutator_le_right.mp
      (hWA.trans ((normal_subgroupOf_iff_le_normalizer hYA).mp hYN))
  have hspan : conjugateSpanBy LH A = Y :=
    source_covering_intersection_orbit D hIM hIH hI.1.1.2.2.1 horbit
  have hcore := core_join_eq_of_sectionSylow hYA hYN hpY hSY
  have hNV := lemma_4_1_5_2 hyp S hWne hdata.1 rfl
  refine
    { sqtk := D.simpleQTKE.twoLocal_sqtk hH.1
      radical_isTwoGroup := isPGroup_pCoreIn 2 I
      radical_le := hRA
      local_le := inf_le_left
      local_fitting := lemma_4_1_4_6 hyp hminus hI hmem hIH hout
      core_nontrivial := hmem
      component_le := hLHA
      component := (source_covering_intersection_component D hIM hIH hI.1.1.2.2.1).1
      section_sylow := ?_
      characteristic_control := ?_
      module_nontrivial := hWne
      module_elementary := hdata.2.1
      module_le := ?_
      module_commutator := ?_
      module_central := ?_
      module_normalizer := le_inf inf_le_left (inf_le_right.trans hNV) }
  · change ∃ S' : Sylow 2 (ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH A) A), _
    rw [hspan,← sectionCentralizerIn_eq_twoSectionCentralizer]
    exact hSY
  · have hc := characteristicNormalizerClosure_subgroupOf_le (hRA.trans inf_le_left)
      (lemma_4_1_4_2 hyp hminus hI)
    intro x hx
    exact ⟨x.property,hc hx⟩
  · change W ≤ conjugateSpanBy LH A
    rwa [hspan]
  · change W = ⁅W,conjugateSpanBy LH A⁆
    rwa [hspan]
  · change W ≤ (center ((conjugateSpanBy LH A ⊔ R).pCoreIn 2)).map _
    rw [hspan,hcore]
    exact hWcenter
end CFSG.Quasithin.Chapter10
