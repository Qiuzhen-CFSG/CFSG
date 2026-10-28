module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourKnownSimple

/-!
# The original terminal classification with its embedding input discharged

This is the source-specialized interface for `ClassificationComplete`.
`OmegaKnownSimple` constructs the exceptional seed using the proved seed
normalizer, 13.5.7 and abelian-closure results. `LiftingKnownSimple` uses the
full restricted Sylow and the actual ambient two-core map to obtain a normal
containing component. The exceptional catalogue permits a J₄ quotient in
addition to the terminal candidates; `JankoFourKnownSimple` excludes it by
the faithful action of the original singular-centralizer quotient.

Consequently no universal A.3.12 theorem or replacement embedding hypothesis
is needed. The original Context, two centralizer conditions, counterexample
and genuine earlier 5.2.3 theorem are the inputs. The latter is supplied by
the independent classifier; this module does not prove 5.2.3 or Theorem D.

Source: Aschbacher–Smith, 13.6.27 and its terminal paragraph, pp.934–935.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
  (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
  (hcounter : IsA5Counterexample G)
  (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
include d hCv houtside hcounter h523

/-- The original classification endpoint with all A.3.12 uses discharged
on the actual source context. The full catalogue retains field-two endpoints. -/
theorem source_qtkeModel_of_A5_counterexample_knownSimple :
    ClassificationModels.IsQTKEModel G :=
  source_qtkeModel_of_source523 d hCv houtside hcounter h523

/-- The same original source endpoint in the complete guarded catalogue. -/
theorem source_knownSimple_of_A5_counterexample_knownSimple : KnownSimple.IsKnownSimple G :=
  ⟨inferInstance, d.hypothesis.qtke.simple,
    (source_qtkeModel_of_A5_counterexample_knownSimple d hCv houtside hcounter h523).isKnownSimpleCarrier⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
