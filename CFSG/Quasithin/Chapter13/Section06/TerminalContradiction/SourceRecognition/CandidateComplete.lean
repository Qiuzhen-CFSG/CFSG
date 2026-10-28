module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateStructure

/-!
# The terminal A₅ contradiction from the actual component candidate

The original involution-centralizer family supplies SQTK. The actual
candidate then supplies its own normality and quasisimple two-core quotient,
so neither property is an extra premise in the terminal source application.
The elementary structure of V likewise comes from the original chosen module.

The component candidate, genuine earlier A.3.12 and 5.2.3, nonsingular
centralizer bound and singular escape remain explicit source obligations.
Source: Aschbacher–Smith, Lemma 13.6.27 and the following paragraph,
printed pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The literal exceptional candidate suffices for the terminal source
argument; its normality and quotient quasisimplicity are derived here. -/
theorem terminal_contradiction_of_A5_candidate_source
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (h523 : Components.SuzukiIsolation.Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K) :
    False := by
  let := d.elementary
  let := hc.quotient_isQuasisimple hK
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  let := hc.normal hK (Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1)
  exact terminal_contradiction_of_A5_source523 d hA312 hCv houtside hcounter h523 hK hc

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
