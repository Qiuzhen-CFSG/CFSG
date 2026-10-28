module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ClassificationComplete

/-!
# Applying the existing A₅ and A₆ source interfaces to the final dispatcher

The A₆ adapter uses the original central quotient L/O₂,Z(L) in both the
ordinary and triple-cover rows; the latter is not treated as L/O₂(L).
For A₅, failure of the full Main-Theorem list supplies both global exclusions
in `IsA5Counterexample`. The current terminal theorem then applies to the
original Context, nonsingular-point centralizer and singular-line escape.

Context construction and the earlier A.3.12/5.2.3 implications remain explicit.
This adapter records the literal uses in the current terminal export; the
dispatcher also accepts a specialized A₅ proof that discharges these inputs.
Source: Aschbacher--Smith 13.6.1, 13.6.27, 13.8.1 and 14.8.1.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section06.CentralizerReduction
open Chapter13.Section06.CentralizerReduction.A5Module
open Chapter13.Section05.A5Source
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Chapter14.Section03.FaithfulSource

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the original 13.8.1 central-quotient contract to both catalogue rows. -/
theorem sixRecognition_of_theorem1381 (source1381 : Theorem1381.{u}) :
    SixRecognition G := by
  intro T L _ hmax hmodel
  apply source1381 G T L (hypothesis1331 hmax.1)
  rcases hmodel with h6 | hc6
  · exact A6_centralQuotient_of_coreQuotient L h6
  · obtain ⟨e⟩ := hc6.2.2
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
    refine ⟨centralQuotient_equiv_of_cover L f
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_⟩
    ext x
    change e (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) x) = 1 ↔
      x ∈ center (L ⧸ pCore 2 L)
    rw [e.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- The earlier A₅ producers must construct the genuine Context and the two
centralizer conclusions on its same marked module and singular line. -/
def FiveContextInput (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Maximal (Counterexample T) L →
    Chapter1.Section02.LocalModels.IsAlternating (L ⧸ pCore 2 L) 5 →
    IsA5Counterexample G →
    ∃ (V V₁ V₂ V₃ : Subgroup G) (d : Context T L V V₁ V₂ V₃),
      centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G) ∧
      ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G)

/-- Failure of the complete model list gives precisely the two exclusions
required by the existing A₅ terminal source export. -/
theorem fiveRecognition_of_source_context
    (contexts : FiveContextInput G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) : FiveRecognition G := by
  classical
  intro T L hmany hmax h5
  by_contra hnot
  have hcounter : IsA5Counterexample G :=
    ⟨fun hu => hnot ((IsTheoremDModel.exceptional (.unitary_binary hu)).toQTKEModel),
      fun hl => hnot ((IsTheoremDModel.exceptional (.linear_three hl)).toQTKEModel)⟩
  obtain ⟨V, V₁, V₂, V₃, d, hCv, houtside⟩ := contexts T L hmany hmax h5 hcounter
  exact hnot (Chapter13.Section06.TerminalContradiction.source_qtkeModel_of_A5_counterexample
    d hA312 hCv houtside hcounter h523)

end CFSG.Quasithin.Chapter14.Section08.SourceCases
