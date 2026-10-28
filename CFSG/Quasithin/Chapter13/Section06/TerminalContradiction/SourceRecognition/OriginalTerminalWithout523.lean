module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5SourceExclusion
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalTerminalBorelNormalization
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalIntrinsicLinearResidualExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRightComplete
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalPairExclusion

/-!
# The original A₅ terminal contradiction without earlier5.2.3

The original singular centralizer selects the actual outside H and its
normalized residual. The marked source proves uniqueness over L itself.
The earlier right-factor construction therefore produces the genuine F.1.1
pair with zero completion core and a nontrivial perfect right factor inside
that same H. The proved original terminal pair obstruction gives a
contradiction. No universal earlier5.2.3 classifier or completion-recognition
premise is used.

Source: Aschbacher--Smith 5.2.4--6,13.6.27, pp.649--651,934--935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Section05.A5Source CentralizerReduction CentralizerReduction.A5Module
open Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The actual initial terminal source is impossible under the two original
exceptional-model exclusions, with no earlier5.2.3 premise. -/
theorem original_terminal_contradiction_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) : False := by
  obtain ⟨H,hH,hHC,hgen,_,_,_,hN⟩ :=
    source_initial_normalized_residual_of_context d hCv houtside hcounter hmany
  have hthree := fun hlinear =>
    terminal_contradiction_of_intrinsic_linear_residual d hCv houtside hcounter hH hHC hlinear
  have hi := rankOne_input_of_many d hmany
  obtain ⟨A,B,R,prep,hp⟩ := d.chosen.rankOne_global_preparation_perfect_of_uniqueness
    (rankOne_hypothesis d) hmany (by decide : 1 < 2) hi.linear hH hgen hthree hN
    (Chapter4.Section03.RankOneUniqueness.uniqueness_of_original_a5_context d hmany)
  exact original_terminal_pair_impossible d hH hHC
    (prep.right_le_residual.trans (map_subtype_le _))
    (prep.hypothesisF11 hi hH.1.1.2) hp
    (fun he => prep.right_outside (he ▸ bot_le))

/-- Retain the full Main-Theorem catalogue when removing the two exceptional
model exclusions from the original terminal contradiction. -/
theorem original_terminal_model_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G)) :
    ClassificationModels.IsQTKEModel G := by
  by_cases hu : ClassicalGroup.IsPSU G 4 2
  · exact (ClassificationModels.IsTheoremDExceptionalModel.unitary_binary hu).toQTKEModel
  by_cases hl : ClassicalGroup.IsPSL G 4 3
  · exact (ClassificationModels.IsTheoremDExceptionalModel.linear_three hl).toQTKEModel
  exact (original_terminal_contradiction_without_source523 d hmany hCv houtside ⟨hu,hl⟩).elim

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
