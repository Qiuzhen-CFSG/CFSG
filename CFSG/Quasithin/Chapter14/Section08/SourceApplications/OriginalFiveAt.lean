module

public import CFSG.Quasithin.Chapter14.Section08.SourceApplications.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.SourceAssembly.At

/-!
# FiveRecognition from the original local A₅ source inputs

The actual dispatcher supplies the multiple-overgroup guard and its maximal
counterexample. The latter yields Hypothesis 13.3.1, including the uniform
A₅ clause. Local normalization and the earlier module theorem construct the
chosen module and Context; local 12.2.13 supplies escape at that same flag.
The terminal residual split uses the original Cartan escape and the shared
normalized rank-one construction with explicit uniqueness and recognition.

Thus neither a supplied Context nor universal 13.3.2, 12.2.13 or 5.2.3 is
required. Every earlier input below is requested only in the actual guarded
source configuration. This conditional theorem supplies precisely the
FiveRecognition argument of the existing MainForward/Main local assembly;
its full QTKE catalogue includes the field-two endpoints.

The independent source producers must still discharge all these premises.
Source: Aschbacher--Smith, 13.3.2--5, 13.6.27 and 14.8.1,
pp.884--886,934--935,1078.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Chapter13.Section03.SourceCompletion Chapter13.Section05.A5Source
open Chapter13.Section06.CentralizerReduction Chapter13.Section06.CentralizerReduction.A5Module
open Chapter13.Section06.TerminalContradiction.Components
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Chapter12.Section02 Chapter6.Source.RankOneGeneric
open Chapter14.Section03.FaithfulSource

variable {G : Type*} [Group G] [Finite G]

/-- The genuine local A₅ endpoint for the existing final dispatcher.
The original Hypothesis 13.3.1 and multiple-overgroup guard accompany every
source input; the final construction makes the same choices throughout. -/
theorem fiveRecognition_of_original_local_sources
    (normalization : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1331 T L → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      (T : Subgroup G) ≤ normalizer (L : Set G))
    (modules : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      OriginalAlternatingFiveModules1332At T L)
    (recognition12213 : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem12213At KnownSimple.IsKnownSimple T)
    (hCv : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1331 T L → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      IsA5Counterexample G → ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (hescape : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1331 T L → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      IsA5Counterexample G →
      ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      Context T L V V₁ V₂ V₃ →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
        ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) →
        ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
          normalizer ((pResidual 2 H).map H.subtype : Set G) →
        Source523.LocalAlternative T L H V 2)
    (hunique : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1331 T L → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      IsA5Counterexample G → ∀ X : Subgroup G,
      IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G))
    (hrecognize : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1331 T L → Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      IsA5Counterexample G →
      ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      Context T L V V₁ V₂ V₃ → ∀ H : Subgroup G,
      H ≤ centralizer (V₁ : Set G) →
      Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L,R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : FiveRecognition G := by
  intro T L hmany hmax h5
  have h := hypothesis1331 hmax.1
  obtain ⟨e⟩ := h5
  exact Chapter13.Section06.source_qtkeModel_of_original_A5_sources_at h hmany e
    (normalization T L hmany h ⟨e⟩) (modules T L hmany) (recognition12213 T hmany)
    (hCv T L hmany h ⟨e⟩) (hescape T L hmany h ⟨e⟩)
    (hunique T L hmany h ⟨e⟩) (hrecognize T L hmany h ⟨e⟩)

end CFSG.Quasithin.Chapter14.Section08.SourceCases
