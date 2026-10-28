module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionInvolutionFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionRecognition

/-!
# The complete equality branch of source 6.2.13

Weak closure, the index-two subgroup and its involution fusion supply
Thompson transfer and exclude the elementary-four centralizer alternative.
The constructed extension then gives the marked M/V ≃ S₅ quotient and
CoreData for the actual normal extraspecial subgroup of C_G(z). The
existing marked recognition theorem identifies the ambient group with M₂₂.

Only the published earlier-source LocalAnalysis remains an explicit premise,
as authorized for this branch. Its construction and the strict branch belong
to the final owner `qt-d-1222-rankone-recognition-identification`.
Source: Aschbacher–Smith, 6.2.13, printed pp.686–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- All three transfer premises are now constructed from the source configuration. -/
theorem LocalAnalysis.equality_extension_four_fusion
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (hfour : Nat.card (equalityCentralizer L R z) = 4) :
    EqualityExtensionFourFusion (T : Subgroup G) L R z where
  weak_closure := A.equality_local_core_weakly_closed h611 hnatural hz horder hTH hbranch hfour
  index := A.equality_transfer_subgroup_index h611 hnatural hz horder hTH hbranch hfour
  fusion := fun _ ht ht2 => A.equality_transfer_involution_fusion h611 hnatural hz horder hTH hbranch ht ht2

/-- The complete equality extension: the marked quotient, extraspecial core
and order-two centralizer, with the elementary-four alternative excluded by transfer. -/
theorem LocalAnalysis.equality_extension
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ hnormal : ((layer L R).subgroupOf M).Normal,
      @M22Recognition.CentralizerExtension.CompatibleSymmetricFiveQuotient M inferInstance
        ((layer L R).subgroupOf M) (L.subgroupOf M) hnormal ∧
      M22Recognition.CentralizerExtension.CoreData (equalityCore L R z) ∧
      equalityCentralizer L R z = zpowers z ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = layer L R := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  exact A.equality_extension_of_action_block_fusion h611 hnatural hz horder hTH
    hp.plusType hp.core_center
    (A.equality_extension_action h611 hnatural hz horder hTH hbranch)
    (A.equality_extension_block h611 hnatural hz horder hTH hbranch)
    (A.equality_extension_four_fusion h611 hnatural hz horder hTH hbranch)

/-- Source 6.2.13, equality branch, conditional only on the published earlier local analysis.
The final source owner supplies LocalAnalysis; every equality-branch premise is discharged here. -/
theorem m22_of_local_analysis_of_intersection_eq
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  m22_of_local_analysis_of_intersection_eq_of_four_fusion A h611 hnatural hz horder hTH hbranch
    (A.equality_extension_four_fusion h611 hnatural hz horder hTH hbranch)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
