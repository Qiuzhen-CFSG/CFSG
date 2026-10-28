module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCartanLocalComplete
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalCartanCore

/-!
# Normalization of the original terminal residual

The compatible Cartan pair is constructed from the original chosen module.
Local control has been proved from the actual point-centralizer hypotheses.
The nontrivial central line in the Cartan join then forces the whole relative
Borel to normalize the same residual. The initial H-star selection therefore
already has this normalization, without an earlier 5.2.3 classifier.

Source: Aschbacher--Smith 5.1.9--13 and 13.6.27, pp.634--638,934--935.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Section05.A5Source CentralizerReduction CentralizerReduction.A5Module
open Chapter6.Source.RankOneGeneric Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The full Borel normalizes the original terminal residual. All local
Cartan hypotheses are proved from the same original context. -/
theorem original_terminal_borel_normalizes
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (hgen : 1 < ChapterE.generationParameter H) :
    localBorel T L ≤ normalizer (residual H : Set G) := by
  have hi := rankOne_input_of_many d hmany
  obtain ⟨A,B,c⟩ := d.chosen.rankOne_exists_cartanPair
    (rankOne_hypothesis d) (by decide : 1 < 2) hi.linear hH hgen
  exact original_terminal_borel_normalizes_of_local_control d hH hHC c
    (original_cartan_local_control d hCv houtside hcounter hmany hH hgen c)

/-- Select the actual first outside residual together with its proved
Borel normalization and its original Sylow supplement and normalizer. -/
theorem source_initial_normalized_residual_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) ∧
      1 < ChapterE.generationParameter H ∧
      residual H ⊔ (T : Subgroup G) = H ∧
      ¬ residual H ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (residual H : Set G) ∧
      localBorel T L ≤ normalizer (residual H : Set G) := by
  let := d.elementary
  obtain ⟨H,hH,hHC,hgen,hsup,hout,hT⟩ :=
    source_initial_residual_of_context_knownSimple d hCv houtside hcounter
  exact ⟨H,hH,hHC,hgen,hsup,hout,hT,
    original_terminal_borel_normalizes d hCv houtside hcounter hmany hH hHC hgen⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
