module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalGraphReverse
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFourExclusion

/-!
# Common local analysis with only the independent omega escape outstanding

The proved graph escape excludes the order-sixteen intersection. The
existing actual H-star generation contradiction excludes order four, so
the original core intersection has order eight. LocalAssembly then supplies
all fields of LocalAnalysis on the original subgroups and quotient maps.

Only the earlier source 6.1.5 omega-centralizer escape remains explicit.
Its producer is qt-d-1222-rankone-recognition-natural; final discharge
remains with this local-analysis task. These conditional assembly exports
do not claim that independent premise or the unconditional source theorem.

Source: Aschbacher--Smith, 6.2.1--12, pp.680--686, and its application
in 12.2.2(3d), p.795.
-/

public section

namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The order-eight intersection from source 6.2.8--11, with the graph
escape discharged on the literal original layer. Only the earlier marked
centralizer escape is retained. -/
theorem source_local_core_card_eight_of_centralizer_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8 :=
  source_local_core_card_eight_of_layer_escape D h h611 hnatural hz ho hT
    (source_local_layer_not_le_point_core_of_escape D h h611 hnatural hz ho hT hescape)

/-- All source 6.2.1--12 fields with the sole independent 6.1.5 omega escape
still explicit. No local index, graph, pair or cardinality premise remains. -/
theorem source_local_analysis_of_omega_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (homega : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z := by
  have hline := source_local_centralOmega_eq_zpowers_of_escape h611 hnatural homega hz ho hT
  have hzO : z ∈ centralOmega (T : Subgroup G) := hline.symm ▸ mem_zpowers z
  have he : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
    intro hc
    exact homega ((centralizer_le (Set.singleton_subset_iff.mpr hzO)).trans hc)
  exact source_local_analysis_of_omega_escape_and_core_card D h h611 hnatural homega hz ho hT
    (source_local_core_card_eight_of_centralizer_escape D h h611 hnatural hz ho hT he)

/-- Construct the marked involution and the complete local analysis from
the authorized natural conclusion and the independent earlier omega escape. -/
theorem source_exists_local_analysis_of_omega_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (homega : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ z ∈ ZS (T : Subgroup G) L (wholeReduced T L), orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z := by
  obtain ⟨z,hz,ho,hT⟩ := exists_central_involution_in_ZS h611
  exact ⟨z,hz,ho,hT,source_local_analysis_of_omega_escape D h h611 hnatural homega hz ho hT⟩
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
