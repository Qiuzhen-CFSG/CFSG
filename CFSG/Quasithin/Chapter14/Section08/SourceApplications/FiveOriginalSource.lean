module
public import CFSG.Quasithin.Chapter14.Section08.SourceCases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.CentralizerOriginalSourceComplete

/-!
# Original alternating-five recognition for the full catalogue

The actual original counterexample hypotheses construct a chosen module
and Context. The genuine earlier module clauses at the selected Sylows and
the earlier5.2.3 theorem now suffice: normalization, both outside cases,
nonsingular centralization, singular escape and the selected MS-pair
classification are proved source steps. The conclusion is the full
Main-Theorem catalogue, retaining its field-two endpoints.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Chapter13.Section03.SourceCompletion Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter13.Section06.CentralizerReduction.SourceAssembly
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The A5 dispatcher input has only the genuine earlier module family
and5.2.3 source theorem remaining, with all original local duties proved. -/
theorem fiveRecognition_from_original_module_sources
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) : FiveRecognition G := by
  intro T L hmany hmax hfive
  obtain ⟨a⟩ := hfive
  obtain ⟨V,V₁,V₂,V₃,_,⟨d⟩⟩ := exists_context_from_original_modules
    (hypothesis1331 hmax.1) a hmany (hmodules T L hmany)
  exact original_context_model_from_modules d hmany hmodules h523

end CFSG.Quasithin.Chapter14.Section08.SourceCases
