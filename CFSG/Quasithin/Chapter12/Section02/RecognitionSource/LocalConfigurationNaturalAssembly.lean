module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovement
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationAssembly

/-!
# Conditional assembly of the H-star and natural-action branch

The quotient rank bound supplies movement through the proved 12.2.18 deduction.
The independent nonsolvable exclusion then gives solvability for every H-star
member. An actual escaping member supplies the natural-action recognition input.
The result feeds the unchanged local-configuration consumer.

These are conditional assembly theorems: the H-star witness, the 12.2.7 rank
bound, the 12.2.19 exclusion, and the 12.2.20 natural recognition still have to be
proved by their source producers. In particular no unguarded H-star existence
or unconditional NaturalLocalAnalysis is asserted here.

Source: Aschbacher--Smith, 12.2.18--20 and 12.2.26, printed pp.800--806.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem naturalLocalAnalysis_of_source_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hexists : (Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))).Nonempty)
    (rankStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H)
    (naturalStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Group.IsSolvable H → ¬ V ≤ H.pCoreIn 2 →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
        (Representation.specialLinearNatural (k := ZMod 2) d)) :
    ∃ d, NaturalLocalAnalysis T L V d := by
  have hm : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 := fun H hH =>
    chosen_movement_of_quotient_rank h D structural hnone hTI hH (rankStep H hH)
  have hs : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Group.IsSolvable H := fun H hH => solvableStep H hH (hm H hH)
  obtain ⟨H, hH⟩ := hexists
  obtain ⟨d, hd, ha⟩ := naturalStep H hH (hs H hH) (hm H hH)
  exact ⟨d, hd, ha, ⟨H, hH⟩, hs, hm⟩

theorem localConfiguration_of_natural_source_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hexists : (Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))).Nonempty)
    (rankStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H)
    (naturalStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Group.IsSolvable H → ¬ V ≤ H.pCoreIn 2 →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
        (Representation.specialLinearNatural (k := ZMod 2) d))
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → IsTISubgroup V → ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) : ∃ d, SplitLinearConfiguration L V d := by
  apply localConfiguration_of_source_steps D
    (fun hn ht => naturalLocalAnalysis_of_source_inputs h D structural hn ht
      hexists rankStep solvableStep naturalStep) cyclicStep rigidityStep hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
