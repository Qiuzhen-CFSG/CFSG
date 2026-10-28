module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourKnownSimple

/-!
# The original A5 context reaches the Main Theorem catalogue

The counterexample alternative uses the proved exceptional-source endgame.
The two excluded models, PSU4(2) and PSL4(3), are retained directly in the
complete Main Theorem list. Thus no A5 model-exclusion or embedding callback
is required. The original nonsingular centralizer bound, singular escape,
and genuine 5.2.3 input remain with their source producers.

The final consumer excludes this actual context in a counterexample to the
Main Theorem, without imposing the stricter field bound of standalone D.
Source: Aschbacher--Smith 13.6.1 and the Main Theorem, pp.926,1166.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

theorem source_qtkeModel_of_A5_context
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  by_cases hu : ClassicalGroup.IsPSU G 4 2
  · exact (ClassificationModels.IsTheoremDExceptionalModel.unitary_binary hu).toQTKEModel
  by_cases hl : ClassicalGroup.IsPSL G 4 3
  · exact (ClassificationModels.IsTheoremDExceptionalModel.linear_three hl).toQTKEModel
  exact source_qtkeModel_of_source523 d hCv houtside ⟨hu, hl⟩ h523

theorem false_of_original_A5_context_not_qtkeModel
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hnot : ¬ ClassificationModels.IsQTKEModel G) : False :=
  hnot (source_qtkeModel_of_A5_context d hCv houtside h523)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
