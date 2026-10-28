module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBlockAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAction

/-!
# Chapter 12 consumers of the four-space action

Apply the source 6.2.11 centralizer, displacement and Sylow-supplement
identities to the original whole reduced layer and the closure chosen by the
marked module. The order-four branch remains an explicit input; its ambient
block/A₇ contradiction is still outstanding.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The source centralizer identities, on the original chosen-module layer
and its actual closure, before the block/A₇ contradiction. -/
theorem source_local_four_intersection_mutual_centralizers
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
        centralizer (commutatorLayer T L : Set G) = ZS (T : Subgroup G) L (wholeReduced T L) ∧
      commutatorLayer T L ⊓ centralizer
        (sourceClosure (T : Subgroup G) L (wholeReduced T L) z : Set G) =
          ZS (T : Subgroup G) L (wholeReduced T L) := by
  have hp := (source_local_layer_normalizers D h h611 hnatural).1
  exact ⟨LocalQuotientAction.four_closure_centralizer_layer h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_layer_centralizer_closure h611 hnatural hz ho hT hp hcard⟩

/-- The original four-group action, local-core displacement and centralizer
supplement used in the source's block calculation. -/
theorem source_local_four_intersection_block_action
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    let U := sourceClosure (T : Subgroup G) L (wholeReduced T L) z
    (U ⊓ centralizer (commutatorLayer T L : Set G)).relIndex U = 4 ∧
      ⁅U, (L ⊔ (T : Subgroup G)).pCoreIn 2⁆ ≤ ZS (T : Subgroup G) L (wholeReduced T L) ∧
      (T : Subgroup G) ⊓ centralizer (commutatorLayer T L : Set G) =
        commutatorLayer T L ⊔ ((T : Subgroup G) ⊓
          centralizer ((U ⊔ commutatorLayer T L : Subgroup G) : Set G)) := by
  have hp := (source_local_layer_normalizers D h h611 hnatural).1
  exact ⟨LocalQuotientAction.four_closure_action_index h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_closure_local_core_commutator h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_sylow_centralizer_supplement h611 hnatural hz ho hT hp hcard⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
