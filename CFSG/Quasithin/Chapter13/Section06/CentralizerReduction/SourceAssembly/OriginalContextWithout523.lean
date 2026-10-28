module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.CentralizerIntrinsicSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalTerminalWithout523

/-!
# The original A₅ context reaches the full catalogue from module rows

The intrinsic outside source and the original selected-Sylow module family
give the literal nonsingular centralizer bound and singular-line escape.
The actual terminal pair contradiction then removes the remaining earlier
5.2.3 premise. Both exceptional models remain in the full QTKE catalogue.
The genuine module clauses at every guarded Sylow remain explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module Section05.A5Source Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original Context and genuine guarded module family suffice for
the full Main-Theorem catalogue, with no earlier5.2.3 input. -/
theorem original_context_model_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I) :
    ClassificationModels.IsQTKEModel G := by
  by_contra hno
  have hc : IsA5Counterexample G :=
    ⟨fun hu => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.unitary_binary hu)).toQTKEModel),
     fun hl => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.linear_three hl)).toQTKEModel)⟩
  exact TerminalContradiction.original_terminal_contradiction_without_source523 d hmany
    (original_nonsingular_centralizer_without_source523 d hmany hmodules hc)
    (original_singular_escape_without_source523 d hmany (hmodules T L hmany)) hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
