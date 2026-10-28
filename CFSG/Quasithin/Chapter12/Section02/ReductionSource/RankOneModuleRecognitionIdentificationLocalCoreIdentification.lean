module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreIdentification
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalBlockCore

/-!
# Chapter 12 identification of the original block cores

In the contrary order-four intersection branch, the original closure has
exactly the component Sylow action on the chosen-module layer. Sylow
averaging identifies the two-cores of LT, L and M with that same layer,
and the actual component Sylow is its product with the original closure.

Source: Aschbacher--Smith, 6.2.11, printed p.686. Normalizer premises are
discharged by the marked Chapter 12 setup. The subsequent A₇ contradiction
and the one-sided 6.2.7--8 argument remain outstanding.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The original core and Sylow identities used by the block argument. -/
theorem source_local_four_intersection_core_identification
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = commutatorLayer T L ∧
      L.pCoreIn 2 = commutatorLayer T L ∧
      (normalizer (L : Set G)).pCoreIn 2 = commutatorLayer T L ∧
      (T : Subgroup G) ⊓ L = sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊔
        commutatorLayer T L := by
  obtain ⟨hp, hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  obtain ⟨hL, hM⟩ := LocalQuotientAction.four_component_and_maximal_core_eq_layer
    h611 hnatural hz ho hT hp hNL hcard
  exact ⟨LocalQuotientAction.four_local_core_eq_layer h611 hnatural hz ho hT hp hNL hcard,
    hL, hM, LocalQuotientAction.four_component_sylow_eq_sup h611 hnatural hz ho hT hp hNL hcard⟩

/-- The marked action equality retains the literal closure and whole-reduced layer. -/
theorem source_local_four_intersection_sylow_action
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    ChapterE.inducedAutomizer (commutatorLayer T L)
        (sourceClosure (T : Subgroup G) L (wholeReduced T L) z) =
      ChapterE.inducedAutomizer (commutatorLayer T L) ((T : Subgroup G) ⊓ L) := by
  obtain ⟨hp, hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  exact LocalQuotientAction.four_closure_sylow_action h611 hnatural hz ho hT hp hNL hcard

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
