module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionRecognition

/-!
# Equality recognition on the whole reduced subgroup

The constructed cubic centralizer completes the action calculation and the
order-two case reaches the actual M₂₂ carrier. The conditional application
retains only the remaining order-four weak-closure, index and fusion
obligation, using the literal canonical core and original reduced layer.
Its discharge remains with `qt-d-1222-recognition-equality-geometry`.

Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), printed pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The literal reduced-layer application, retaining only the source's
remaining order-four fusion obligation. -/
theorem reduced_m22_of_equality_four_fusion
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L))
    (hfour : Nat.card (equalityCentralizer L (wholeReduced T L) z) = 4 →
      EqualityExtensionFourFusion (T : Subgroup G) L (wholeReduced T L) z) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  exact m22_of_local_analysis_of_intersection_eq_of_four_fusion A h611 hnatural
    hz horder hTH hbranch hfour

/-- The order-two case reaches M₂₂ on the original whole reduced subgroup. -/
theorem reduced_m22_of_equality_centralizer_two
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L))
    (htwo : Nat.card (equalityCentralizer L (wholeReduced T L) z) = 2) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  exact m22_of_local_analysis_of_intersection_eq_of_centralizer_two A h611 hnatural
    hz horder hTH hbranch htwo

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
