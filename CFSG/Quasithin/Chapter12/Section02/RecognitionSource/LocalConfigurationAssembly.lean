module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationDefs
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationSplitting
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Assembly

/-!
# Conditional local assembly for the original 12.2.13 choice

The three source producers have distinct obligations: the natural action and
solvable H-star analysis; the cyclic TI pair and linear block; and rigidity
together with a complement in the original parabolic. Gaschütz, proved in
`LocalConfigurationSplitting`, promotes this last complement to L.

The resulting implication has exactly the `localStep` type used by the
recognition assembly. The producers remain explicit here: this is not an
unconditional proof of 12.2.17--26 or Theorem 12.2.13.
Source: Aschbacher--Smith, 12.2.17--27, printed pp.800--807.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Compose the three local source implications on the unchanged T, L and V.
Only the local parabolic complement is an input; the complement inside L
is constructed by the proved Gaschütz application. -/
theorem localConfiguration_of_source_steps (D : ChosenModule T L V)
    (naturalStep : NoEscape L V → IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → IsTISubgroup V → ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d := by
  obtain ⟨d, A⟩ := naturalStep hnone hTI
  obtain ⟨H, P, U, C⟩ := cyclicStep d A hnone hTI
  obtain ⟨hrank, hself, hcore, hsplit⟩ := rigidityStep d H P U A C hnone hTI
  exact ⟨d, splitLinearConfiguration_of_parabolic_split D hrank C.block A.natural
    hself hcore hsplit⟩

/-- The actual `localStep` application in `alternatives_of_source_steps`.
Global TI and terminal ambient recognition remain the independent branches
owned by the parent 12.2.13 assembly. -/
theorem alternatives_of_local_source_steps (D : ChosenModule T L V)
    (ti : NoEscape L V → IsTISubgroup V)
    (naturalStep : NoEscape L V → IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → IsTISubgroup V → ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V :=
  alternatives_of_source_steps ti
    (localConfiguration_of_source_steps D naturalStep cyclicStep rigidityStep) recognize

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
