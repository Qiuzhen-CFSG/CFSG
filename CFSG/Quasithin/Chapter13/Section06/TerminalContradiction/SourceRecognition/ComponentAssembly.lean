module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParameterSetup
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextComplete

/-!
# The A₅ exceptional-component endgame on the original context

The constructed source parameter record gives the large-prime core
exclusions in the actual line centralizer. The earlier candidate and
uniqueness proofs therefore feed the literal 13.6.27 extension argument,
which supplies the component conclusion used by the terminal quadratic
ratio contradiction. No separate EarlierA5Setup or Components.Conclusion
witness is assumed.

The actual exceptional candidate, its uniqueness, nonsingular centralizer
bound, singular escape and earlier 13.3.8/A.3.12 statements remain explicit.
These source obligations are not proved by this assembly.
Source: Aschbacher–Smith 13.6.27 and the final argument, printed pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The candidate and uniqueness input to 13.6.27 now uses the literal
centralizer of the original invariant line. All parameter and large-prime
core premises are supplied from the source context. -/
theorem source_component_conclusion_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) (h1338 : Earlier1338Two T)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hu : ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K) :
    Components.Conclusion ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) := by
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hT : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  exact Components.ThreeStructure.conclusion_of_candidate
    (Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1)
    (T.subtype hT) hK hc hu
    (fun p hp hlarge => source_quotient_pCore_eq_bot_of_context d hA312 hCv
      houtside hcounter h1338 (Ratio.residualCentralizer L V₁) _ hH p hp hlarge)

/-- The terminal contradiction reduces the original A₅ source to its
remaining exceptional candidate and uniqueness proofs, without an assumed
13.6.25 setup or a 13.6.27 conclusion. -/
theorem terminal_contradiction_of_A5_candidate
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) (h1338 : Earlier1338Two T)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hu : ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K) : False := by
  exact terminal_contradiction_of_A5_context d hA312 hCv houtside hcounter
    (source_component_conclusion_of_context d hA312 hCv houtside hcounter h1338 hK hc hu)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
