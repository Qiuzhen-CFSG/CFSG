module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionFusionReduction

/-!
# Transfer geometry on the whole reduced subgroup

The order-four alternative gives weak closure of the actual Q=O₂(LT) and
index two of P(T∩L), with the same canonical P inside C_G(z). These
facts reduce equality recognition to the one remaining involution-fusion
assertion on that literal subgroup. Its proof remains with the equality
geometry owner `qt-d-1222-recognition-equality-geometry`.

Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), printed pp.688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- Weak closure and index two for the literal whole-reduced configuration. -/
theorem reduced_equality_transfer_geometry
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L =
      ZS (T : Subgroup G) L (wholeReduced T L))
    (hfour : Nat.card (equalityCentralizer L (wholeReduced T L) z) = 4) :
    (∀ g : G, ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g ≤ (T : Subgroup G) →
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g = (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
    (equalityTransferSubgroup (T : Subgroup G) L (wholeReduced T L) z).relIndex
      (T : Subgroup G) = 2 :=
  ⟨A.equality_local_core_weakly_closed h611 hnatural hz horder hTH hbranch hfour,
    A.equality_transfer_subgroup_index h611 hnatural hz horder hTH hbranch hfour⟩

/-- Equality recognition with only the source involution-fusion step explicit. -/
theorem reduced_m22_of_equality_involution_fusion
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L =
      ZS (T : Subgroup G) L (wholeReduced T L))
    (hfusion : Nat.card (equalityCentralizer L (wholeReduced T L) z) = 4 →
      ∀ t ∈ equalityTransferSubgroup (T : Subgroup G) L (wholeReduced T L) z,
        orderOf t = 2 → IsConj z t) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  m22_of_local_analysis_of_intersection_eq_of_involution_fusion A h611 hnatural
    hz horder hTH hbranch hfusion

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
