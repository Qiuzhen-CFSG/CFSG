module

public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape

/-!
# Assembly of the original A₅ source branch

The Section 13.3 source choice supplies the natural A₅ module and its
invariant flag.  `A5Setup.exists_context_of_one_or_two_modules` turns that
choice into the literal `A5Source.Context`; in particular, the coordinates,
the normalizer action and the three marked subgroups are the ones used by the
13.6 terminal argument.  The remaining hypotheses below are the source
exclusions at the actual selected context: the nonsingular centralizer bound,
the singular escape, and the genuine 5.2.3 classification. The two exceptional
models are retained directly; the centralizer inputs are needed only under
their source counterexample exclusions. The terminal theorem then supplies
the full Main-Theorem catalogue. This route returns `IsQTKEModel`: the
field-two rank-two endpoints in the catalogue are valid Main-Theorem outputs
and cannot be silently strengthened to the narrower Theorem D predicate.
The final application supplies singular escape from the original 12.2.13
vector alternative by the two nonzero A₅ orbits.

Source: Aschbacher--Smith, 13.3.2--13.3.3 and 13.6.1, printed
pp.884--886 and 926--935. These are conditional Main-Theorem applications;
they do not assert the narrower two-model conclusion of 13.6.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06
open CentralizerReduction CentralizerReduction.A5Module
open Section03.A5Setup
open Section05.A5Source
open TerminalContradiction
open TerminalContradiction.Components.SuzukiIsolation
open Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The natural A₅ source choice and the two centralizer conditions at its
constructed flag give the full Main-Theorem model.

The two predicates are quantified over the flag constructed by the source
setup rather than over an unrelated record projection.  Thus the caller must
provide the literal centralizer inclusions for the same `Context` consumed by
the terminal argument. -/
theorem source_qtkeModel_of_natural_A5_source
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L V)
    (hCv : IsA5Counterexample G → ∀ (V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : IsA5Counterexample G → ∀ (V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ _d : Context T L V V₁ V₂ V₃,
        ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  classical
  by_cases hu : ClassicalGroup.IsPSU G 4 2
  · exact (ClassificationModels.IsTheoremDExceptionalModel.unitary_binary hu).toQTKEModel
  by_cases hl : ClassicalGroup.IsPSL G 4 3
  · exact (ClassificationModels.IsTheoremDExceptionalModel.linear_three hl).toQTKEModel
  have hc : IsA5Counterexample G := ⟨hu, hl⟩
  obtain ⟨V₁, V₂, V₃, h23, ⟨d⟩⟩ :=
    exists_context_of_one_or_two_modules h d hmodel
  exact source_qtkeModel_of_source523 d (hCv hc V₁ V₂ V₃ h23 d)
    (houtside hc V₁ V₂ V₃ h23 d) hc h523

/-- In the original counterexample, normalization selects an Irr⁺ module.
The genuine earlier module classifier identifies its action, after which the
flag and terminal argument are constructed on that same subgroup. -/
theorem source_qtkeModel_of_A5_module_classification
    (h : Counterexample T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hCv : IsA5Counterexample G → ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : IsA5Counterexample G → ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ _d : Context T L V V₁ V₂ V₃,
        ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  have hsource := Chapter14.Section03.FaithfulSource.hypothesis1331 h
  obtain ⟨V, ⟨d⟩⟩ :=
    (OriginalMaximality.hypothesis1221 hsource e).exists_chosen_of_normalizes hn
  have hmodel := hmodules G T L h L h.local_component ⟨e⟩ V d
  exact source_qtkeModel_of_natural_A5_source hsource d (Or.inl hmodel)
    (fun hc => hCv hc V) (fun hc => houtside hc V) h523

/-- Original 12.2.13 supplies an escaping vector; the two A₅ orbits and
the nonsingular bound move that escape to the literal flag line. -/
theorem source_qtkeModel_of_A5_source12213
    (h : Counterexample T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hCv : IsA5Counterexample G → ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  apply source_qtkeModel_of_A5_module_classification h e hn hmodules hCv ?_ h523
  intro hc V V₁ V₂ V₃ h23 d
  exact singular_escape_of_vector_escape d (hCv hc V V₁ V₂ V₃ h23 d)
    (vector_escape_of_source12213 d h12213)

end CFSG.Quasithin.Chapter13.Section06
