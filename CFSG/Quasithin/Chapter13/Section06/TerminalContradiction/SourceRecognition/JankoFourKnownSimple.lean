module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourSeed
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourAction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourUniqueness
/-!
# The original A₅ source classification without A.3.12

The normalized exceptional seed produces either an ordinary terminal candidate,
a normal quasisimple J₄ quotient, or a genuine global alternative of 5.2.3.
The ordinary candidates have already been excluded. In the J₄ case, the
original source and 5.2.3 isolate its component; the prime-core deductions
and full innerness of J₄ identify the entire singular-centralizer quotient.
Its faithful binary action has quadratic ratio at most two, contradicting
the concrete J₄ action bound. Thus only the global known models remain.

No exceptional embedding callback or J₄ exclusion is assumed. The genuine
earlier 5.2.3 theorem remains the explicit independent source input.
Source: Aschbacher–Smith 13.6.27 and its terminal paragraph, pp.934–935.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
  (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
  (hcounter : IsA5Counterexample G)
  (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
include d hCv houtside hcounter h523

/-- The remaining actual normal J₄ component is impossible in the source context. -/
theorem terminal_contradiction_of_A5_source523_jankoFour
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) : False := by
  let := d.elementary
  exact terminal_contradiction_of_A5_jankoFour_of_unique d hCv houtside hcounter hK e
    (source_component_unique_of_jankoFour d hCv houtside hcounter h523 hK e)

/-- The local alternatives are impossible, leaving the genuine global 5.2.3 models. -/
theorem source_globalAlternative_of_source523 : Source523.GlobalAlternative G := by
  rcases source_jankoFour_quasisimple_or_global d hCv houtside hcounter h523 with hl | hg
  · obtain ⟨K, hK, hn, hq, ⟨e⟩⟩ := hl
    let := hn
    let := hq
    exact (terminal_contradiction_of_A5_source523_jankoFour d hCv houtside hcounter h523 hK e).elim
  · exact hg

/-- The resulting global alternatives are literal members of the Main Theorem catalogue. -/
theorem source_qtkeModel_of_source523 : ClassificationModels.IsQTKEModel G := by
  rcases source_globalAlternative_of_source523 d hCv houtside hcounter h523 with hm | ⟨f, hf⟩
  · exact .sporadic ⟨.m23, hm⟩
  · exact .rank_two f hf

/-- The complete original exceptional-source classification retains only genuine 5.2.3. -/
theorem source_knownSimple_of_source523 : KnownSimple.IsKnownSimple G := by
  exact ⟨inferInstance, d.hypothesis.qtke.simple,
    (source_qtkeModel_of_source523 d hCv houtside hcounter h523).isKnownSimpleCarrier⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
