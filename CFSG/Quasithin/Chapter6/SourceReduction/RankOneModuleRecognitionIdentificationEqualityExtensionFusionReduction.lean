module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionTransferGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionRecognition

/-!
# Equality recognition reduced to involution fusion

In the order-four centralizer alternative, the elementary local core Q is
weakly closed in T and P(T∩L) has index two. The remaining source step is
fusion of the involutions of P(T∩L) to z. Supplying that step now applies
Burnside fusion and Thompson transfer, excludes the four-group alternative,
and reaches the actual M₂₂ carrier through the constructed extension geometry.

The involution-fusion proof and final equality assembly remain with
`qt-d-1222-recognition-equality-geometry`; this is a conditional reduction.
Source: Aschbacher–Smith, proof of 6.2.13, printed p.688.
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The elementary-four branch retains only its involution-fusion assertion.
The weak-closure and index premises of transfer are constructed here. -/
theorem m22_of_local_analysis_of_intersection_eq_of_involution_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfusion : Nat.card (equalityCentralizer L R z) = 4 →
      ∀ t ∈ equalityTransferSubgroup (T : Subgroup G) L R z,
        orderOf t = 2 → IsConj z t) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  apply m22_of_local_analysis_of_intersection_eq_of_four_fusion A h611 hnatural hz horder hTH hbranch
  intro hfour
  exact {
    weak_closure := A.equality_local_core_weakly_closed h611 hnatural hz horder hTH hbranch hfour
    index := A.equality_transfer_subgroup_index h611 hnatural hz horder hTH hbranch hfour
    fusion := hfusion hfour }

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
