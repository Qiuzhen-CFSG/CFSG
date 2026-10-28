module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextComplete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.J2Uniqueness

/-!
# The original A₅ terminal contradiction in the J₂ branch

The actual line centralizer is SQTK. Its original J₂ candidate has full
three-rank and five-rank, so the component-isolation argument proves
uniqueness directly. The existing original13.6.26 and component extension
then supply the literal13.6.27 conclusion used by the terminal quadratic
ratio contradiction.

The earlier A.3.12 containment input, nonsingular centralizer bound,
singular escape and counterexample remain exactly as in the original
source consumer. The J₂ branch requires neither5.2.3 nor a mixed-amalgam
recognition assumption, and normality of the candidate is not an input.
Source: Aschbacher–Smith13.6.25–27 and the terminal paragraph, pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Direct component uniqueness in the original J₂ line-centralizer branch. -/
theorem source_j2_component_unique
    (d : Context T L V V₁ V₂ V₃)
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) :
    ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K := by
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  exact Components.SuzukiIsolation.component_unique_of_j2
    (Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1) hK e

/-- The original J₂ terminal branch, with its former5.2.3 premise discharged. -/
theorem terminal_contradiction_of_A5_j2
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let := d.elementary
  exact terminal_contradiction_of_A5_context d hA312 hCv houtside hcounter
    (source_component_conclusion_of_context_native d hA312 hCv houtside hcounter
      hK (Or.inl ⟨e⟩) (source_j2_component_unique d houtside hK e))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
