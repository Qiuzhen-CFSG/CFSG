module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextComplete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.OriginalUniqueness

/-!
# The original A₅ terminal contradiction after source 5.2.3

The original source context supplies the earlier parameter setup and both
13.6.26 clauses. The genuine earlier 5.2.3 theorem and the original ambient
model exclusions make the exceptional component unique. Its actual
three-prime extension therefore yields the component conclusion consumed
by the proved terminal quadratic-ratio contradiction.

No independent coordinate, fusion, abelian-closure, parameter, 13.3.8,
large-prime core, component-uniqueness or final component-conclusion witness
remains. The source candidate, its normality and quasisimple quotient,
nonsingular centralizer bound, singular escape, actual counterexample,
and genuine earlier A.3.12 and 5.2.3 remain the precise inputs.
This does not assert their missing source proofs or full 13.6.1.
Source: Aschbacher–Smith 13.6.25–27 and its terminal paragraph, pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual original line centralizer has no second component once the
source 5.2.3 theorem is applied; the ambient model exclusions come from d. -/
theorem source_component_unique_of_context
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
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K) :
    ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K := by
  obtain ⟨s, hs, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  have hC : centralizer ({s.z.val} : Set G) = centralizer (V₁ : Set G) := by
    rw [← hs, zpowers_eq_closure, centralizer_closure]
  have hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      (Ratio.residualCentralizer L V₁) (T : Subgroup G)
      (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)) := by
    rw [hC]
    exact SourceAbelian.point_centralizer_mem_family d houtside
  have haux : ∀ K' : Subgroup (centralizer ({s.z.val} : Set G)),
      K'.IsCComponent → K'.Normal → IsQuasisimple (K' ⧸ pCore 2 K') →
      Components.Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K' →
      ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K' := by
    intro K' hK' hn hq hc'
    let := hn
    let := hq
    exact Components.SuzukiIsolation.component_unique_of_original_source523
      d s h523 (Ratio.residualCentralizer L V₁) hH hK' hc'
  have haux' : ∀ K' : Subgroup (centralizer (V₁ : Set G)),
      K'.IsCComponent → K'.Normal → IsQuasisimple (K' ⧸ pCore 2 K') →
      Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K' →
      ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K' := by
    exact hC ▸ haux
  exact haux' K hK inferInstance inferInstance hc

/-- Apply the earlier 5.2.3 classification and the original ambient exclusions
to the terminal A₅ argument. Only the actual exceptional candidate remains. -/
theorem terminal_contradiction_of_A5_source523
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
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K) :
    False := by
  exact terminal_contradiction_of_A5_context d hA312 hCv houtside hcounter
    (source_component_conclusion_of_context_native d hA312 hCv houtside hcounter hK hc
      (source_component_unique_of_context d hA312 hCv houtside hcounter h523 hK hc))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
