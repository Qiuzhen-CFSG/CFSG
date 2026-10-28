module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFourExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalMinimal

/-!
# Excluding the original order-four core intersection

The actual H-star subgroup produced in the contrary branch has an elementary
lift of a full Sylow subgroup of its normal A₅ image. The E-generation
obstruction therefore contradicts Hypothesis 6.1.1 on that same subgroup.
This supplies the order-four exclusion without relying on the invalid
quotient-only form of the numerical E.2.2 inference.

Together with the still-explicit 6.2.8 layer escape, the core intersection
has order eight. The full LocalAnalysis assembly below retains both source
escapes: 6.1.5 omega-centralizer escape and 6.2.8 layer escape. Their
unconditional discharge is not asserted here.

Source: Aschbacher--Smith, 6.2.8--12, printed pp.684--686.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The actual H-star contradiction excludes order four. -/
theorem source_local_four_intersection_impossible
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) ≠ 4 := by
  obtain ⟨hp,hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  exact LocalQuotientAction.four_intersection_false h611 hnatural hz ho hT hp hNL le_rfl

/-- Source 6.2.11's count, with only the earlier 6.2.8 escape outstanding. -/
theorem source_local_core_card_eight_of_layer_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ commutatorLayer T L ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8 := by
  obtain ⟨hp,hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  exact LocalQuotientAction.core_card_eight_of_layer_escape
    h611 hnatural hz ho hT hp hNL le_rfl hescape

/-- Every common-analysis field, retaining exactly the independent 6.1.5
omega escape and the still-open 6.2.8 layer escape. -/
theorem source_local_analysis_of_omega_escape_and_layer_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (homega : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ commutatorLayer T L ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z :=
  source_local_analysis_of_omega_escape_and_core_card D h h611 hnatural homega hz ho hT
    (source_local_core_card_eight_of_layer_escape D h h611 hnatural hz ho hT hescape)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
