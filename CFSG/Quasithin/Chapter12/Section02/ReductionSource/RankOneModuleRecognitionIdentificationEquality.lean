module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentification
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityTransfer

/-!
# Equality-branch preparation on the original reduced module

Apply the commutator calculation and natural hyperplane geometry to the
literal whole reduced subgroup from Chapter 12. The transfer application
uses the same canonical normal closure and two-core in C_G(z), the same
O₂(LT), and the actual index-two subgroup P(T ∩ L).

The local-analysis premise belongs to its earlier-source producer. The
transfer premises are the remaining extension and fusion geometry of
6.2.13; this module does not assert their construction or the M₂₂ conclusion.

Source: Aschbacher--Smith, 6.2.13 and 12.2.2(3d), printed pp.687--688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The first equality-branch calculation on the whole R₂(LT) layer,
together with the constructed cubic and its exact hyperplane intersection. -/
theorem reduced_equality_commutator_and_cubic_geometry
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L))
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    ⁅commutatorLayer T L, sourceClosure (T : Subgroup G) L (wholeReduced T L) z⁆ =
      ZS (T : Subgroup G) L (wholeReduced T L) ∧
    ∃ d ∈ L, d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧ orderOf d = 3 ∧
      let B := commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2
      ⁅B, (T : Subgroup G) ⊓ L⁆ = ZS (T : Subgroup G) L (wholeReduced T L) ∧
      B ⊓ B.map (MulAut.conj d⁻¹).toMonoidHom =
        ZS (T : Subgroup G) L (wholeReduced T L) := by
  exact ⟨A.layer_closure_commutator_eq_plane h611 hnatural hz hTH hbranch,
    A.core_intersection_cubic_geometry h611 hnatural hz⟩

/-- The actual reduced-layer transfer consumer. The extension owner must
construct all displayed premises before excluding its elementary-four case. -/
theorem reduced_elementary_four_centralizer_excluded
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hQ : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hDQ : equalityCentralizer L (wholeReduced T L) z ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hDV : equalityCentralizer L (wholeReduced T L) z ⊓ commutatorLayer T L ≤ zpowers z)
    (hweak : ∀ g : G,
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g ≤ (T : Subgroup G) →
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).conjBy g = (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hnorm : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (commutatorLayer T L : Set G))
    (hindex : (equalityTransferSubgroup (T : Subgroup G) L (wholeReduced T L) z).relIndex
      (T : Subgroup G) = 2)
    (hfusion : ∀ t ∈ equalityTransferSubgroup (T : Subgroup G) L (wholeReduced T L) z,
      orderOf t = 2 → IsConj z t) :
    Nat.card (equalityCentralizer L (wholeReduced T L) z) ≠ 4 := by
  exact elementary_four_centralizer_excluded h611 hz horder hQ hDQ hDV
    hweak hnorm hindex hfusion

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
