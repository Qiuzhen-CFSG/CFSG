module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionLayer

/-!
# Normality of the actual equality layer in Chapter 12

The canonical extraspecial pair detects [O₂(LT),L] = V on the literal
whole reduced subgroup. This makes V normal in M and identifies its full
normalizer with M. It also removes the normalizer premise from the
order-four transfer calculation. The quotient and fusion arguments remain
with the equality-geometry owner.
Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The layer normality and normalizer inputs on the original Chapter12 setup. -/
theorem reduced_equality_layer_normality
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = commutatorLayer T L ∧
      ((commutatorLayer T L).subgroupOf (normalizer (L : Set G))).Normal ∧
      normalizer (commutatorLayer T L : Set G) = normalizer (L : Set G) ∧
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
        normalizer (commutatorLayer T L : Set G) := by
  exact ⟨A.equality_local_core_commutator h611 hnatural hz horder hTH hbranch,
    A.equality_layer_normal h611 hnatural hz horder hTH hbranch,
    A.equality_layer_normalizer_eq h611 hnatural hz horder hTH hbranch,
    A.equality_core_normalizer_normalizes_layer h611 hnatural hz horder hTH hbranch⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
