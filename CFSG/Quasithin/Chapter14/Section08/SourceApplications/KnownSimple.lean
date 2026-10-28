module

public import CFSG.Quasithin.Chapter14.Section08.SourceApplications
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ClassificationKnownSimple

/-!
# The A₅ dispatcher application with the embedding input discharged

Failure of the full model catalogue supplies the two original A₅
counterexample exclusions. The same Context and its two centralizers then
feed the current source-specialized terminal theorem. Its proved seed,
component lifting and J₄ argument remove the earlier universal A.3.12 input.
The original context construction and genuine 5.2.3 classifier remain explicit.

This theorem supplies the A₅ input of the local Chapter14/Main dispatcher;
it does not strengthen its full-model output to the narrower D catalogue.
Source: Aschbacher--Smith, 13.6.27 and 14.8.1, pp.934--935 and 1078.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases

open Subgroup ClassificationModels
open Chapter13.Section06.CentralizerReduction
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the current source terminal export to the literal Context and
centralizers. Every embedding premise has already been proved upstream. -/
theorem fiveRecognition_of_source_context_knownSimple
    (contexts : FiveContextInput G)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) : FiveRecognition G := by
  classical
  intro T L hmany hmax h5
  by_contra hnot
  have hcounter : IsA5Counterexample G :=
    ⟨fun hu => hnot ((IsTheoremDModel.exceptional (.unitary_binary hu)).toQTKEModel),
      fun hl => hnot ((IsTheoremDModel.exceptional (.linear_three hl)).toQTKEModel)⟩
  obtain ⟨V, V₁, V₂, V₃, d, hCv, houtside⟩ := contexts T L hmany hmax h5 hcounter
  exact hnot
    (Chapter13.Section06.TerminalContradiction.source_qtkeModel_of_A5_counterexample_knownSimple
      d hCv houtside hcounter h523)

end CFSG.Quasithin.Chapter14.Section08.SourceCases
