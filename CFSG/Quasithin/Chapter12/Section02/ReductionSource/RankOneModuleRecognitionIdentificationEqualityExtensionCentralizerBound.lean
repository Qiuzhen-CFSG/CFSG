module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionPermutationCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizerBound

/-!
# The equality centralizer alternatives for Chapter 12

On the literal whole reduced subgroup, PQ has index two in T and D has
order two or four. This supplies the cardinality branch of the block
calculation. The four-group alternative remains a transfer obligation.
Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The source order alternatives, before the elementary-four exclusion. -/
theorem reduced_equality_centralizer_bound
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    ((equalityCore L (wholeReduced T L) z).map (centralizer ({z} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (T : Subgroup G) = 2 ∧
      (Nat.card (equalityCentralizer L (wholeReduced T L) z) = 2 ∨
        Nat.card (equalityCentralizer L (wholeReduced T L) z) = 4) := by
  exact ⟨A.equality_core_local_join_index h611 hnatural hz horder hTH hbranch,
    A.equality_centralizer_card h611 hnatural hz horder hTH hbranch⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
