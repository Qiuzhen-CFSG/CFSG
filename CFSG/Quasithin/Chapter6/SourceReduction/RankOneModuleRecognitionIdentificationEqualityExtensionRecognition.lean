module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionBlock
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionAssembly

/-!
# Equality recognition after the extension calculation

The canonical pair, extension quotient and cubic centralizer now construct
the full action contract. Combining it with the marked S₅ block reaches
the actual M₂₂ carrier in the order-two centralizer case. The general
conditional assembly retains only the source's order-four weak closure,
index and involution fusion. It applies the actual transfer exclusion
before constructing CoreData and using the marked recognition theorem.

The remaining fusion producer and the final equality-branch assembly stay
with `qt-d-1222-recognition-equality-geometry`. LocalAnalysis is supplied to
the enclosing source theorem by its existing earlier-source producer.
Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The complete action calculation, including the constructed cubic centralizer. -/
theorem LocalAnalysis.equality_extension_action
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    EqualityExtensionAction (T : Subgroup G) L R z := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  exact {
    sylow_centralizer := A.equality_sylow_layer_centralizer h611 hnatural hz hTH hp.plusType
    core_centralizer := A.equality_core_centralizer h611 hnatural hz
    quotient := A.equality_extension_quotient h611 hnatural hz horder hTH hbranch
    cubic_centralizer := A.equality_cubic_centralizer h611 hnatural hz horder hTH hbranch }

/-- All equality geometry is constructed except the explicit order-four
fusion obligation. Its producer remains with the equality-geometry owner. -/
theorem m22_of_local_analysis_of_intersection_eq_of_four_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfour : Nat.card (equalityCentralizer L R z) = 4 →
      EqualityExtensionFourFusion (T : Subgroup G) L R z) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have ha := A.equality_extension_action h611 hnatural hz horder hTH hbranch
  have hb := A.equality_extension_block h611 hnatural hz horder hTH hbranch
  obtain ⟨hn,hq,hP,_,_⟩ := A.equality_extension_of_action_block_fusion h611 hnatural hz horder
    hTH hp.plusType hp.core_center ha hb hfour
  let := hn
  apply m22_of_source_geometry_without_cubic h611 hnatural (centralizer ({z} : Set G)) z rfl
    hTH hq (equalityCore L R z) hP hp.natural_orbit ?_ hp.plane_le_core
    (equalityCore_le_sylow hTH) hbranch
  rw [hp.core_center]
  exact subgroupOf_mono _ (zpowers_le.mpr hz)

/-- The order-two centralizer branch of source 6.2.13 reaches the actual
Mathieu carrier. The separate order-four exclusion is not assumed here. -/
theorem m22_of_local_analysis_of_intersection_eq_of_centralizer_two
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (htwo : Nat.card (equalityCentralizer L R z) = 2) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  apply m22_of_local_analysis_of_intersection_eq_of_four_fusion A h611 hnatural hz horder hTH hbranch
  intro hfour
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
