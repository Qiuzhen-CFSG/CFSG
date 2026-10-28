module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionMarking
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionPairSource
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovementAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleInputs

/-!
# Solvable natural recognition and guarded H-star assembly

The full-axis construction and the seven-row order exclusion now give the
natural action through the original L/O₂(L), in degree three, four or five,
from a solvable moving H-star member. This discharges the axis and marking
inputs in the original naturalStep consumer.

For the same ambient G,T, the multiple-overgroup guard supplies an escaping
H-star member. The local movement theorem and natural recognition then feed
the unchanged split-configuration assembly. These latter theorems remain
conditional on the 12.2.7 quotient-rank bound and the 12.2.19 nonsolvable
exclusion, both still owned by qt-d-12213-hstar-natural. The independent
cyclic and rigidity conclusions remain with the final local-configuration
owner. No unguarded existence or complete 12.2.18–20 source proof is asserted.

Source: Aschbacher–Smith 12.2.18–20 and 12.2.26, printed pp.800–806,
with the standing multiple-overgroup hypothesis after 2.1.1.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked natural row, obtained from the earlier seven-module theorem
and fullness of the literal join action. -/
theorem chosen_natural_marking_of_join_full_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hf : letI := D.elementary
      (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
      D.quotientAction (Representation.specialLinearNatural (k := ZMod 2) d)) :=
  chosen_natural_marking_of_join_full h D _ (modules L V h D) hf

/-- The natural-action implication of 12.2.20. Solvability and movement are
the explicit conclusions of the preceding H-star argument; no axis or marking
callback remains. -/
theorem natural_action_of_solvable_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) :=
  natural_action_of_solvable_movement_and_marking h D structural hnone hTI hH hs hm
    (chosen_natural_marking_of_join_full_at h D structural modules)

/-- The post-2.1.1 multiple-overgroup guard supplies the original escaping
H-star member. The still-open 12.2.7 rank and 12.2.19 nonsolvable exclusion
remain with qt-d-12213-hstar-natural; no universal existence is asserted. -/
theorem naturalLocalAnalysis_of_many_and_hstar_source_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (rankStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H) :
    ∃ d, NaturalLocalAnalysis T L V d := by
  have hm : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 := fun H hH =>
    chosen_movement_of_quotient_rank_at h D structural hnone hTI hH (rankStep H hH)
  have hs : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Group.IsSolvable H := fun H hH => solvableStep H hH (hm H hH)
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany)
  obtain ⟨d, hd, ha⟩ := natural_action_of_solvable_movement h D structural modules
    hnone hTI hH (hs H hH) (hm H hH)
  exact ⟨d, hd, ha, ⟨H, hH⟩, hs, hm⟩

/-- Actual application to the unchanged local-configuration consumer. The
remaining source arguments are explicit and final discharge stays with the
natural and local-configuration assembly owners. -/
theorem localConfiguration_of_many_and_hstar_source_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (rankStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → IsTISubgroup V → ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) : ∃ d, SplitLinearConfiguration L V d := by
  apply localConfiguration_of_source_steps D
    (fun hn ht => naturalLocalAnalysis_of_many_and_hstar_source_at h D structural modules
      hmany hn ht rankStep solvableStep) cyclicStep rigidityStep hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
