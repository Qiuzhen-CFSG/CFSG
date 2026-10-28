module

public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalNormalizedAt

/-!
# Original A₅ assembly from local earlier inputs

Normalization first selects an actual Irr⁺ module. The A₅ clause of
13.3.2 at the original G,T,L identifies its action; the proved flag
construction supplies the invariant Context. Local 12.2.13 and the two
nonzero A₅ orbits give singular escape on that very Context and marking.
The residual split then consumes the separate Cartan and normalized
rank-one branches, without a universal 5.2.3 callback.

All source hypotheses, including Hypothesis 13.3.1 and the multiple-overgroup
guard, are retained. Nonsingular centralizer control, normalization, the
local module/12.2.13 inputs, Cartan escape, uniqueness and completion
recognition remain independent earlier premises. The conclusion is the full
Main-Theorem catalogue, not the narrower two-model assertion of 13.6.1.
Source: Aschbacher--Smith, 13.3.2--5 and 13.6.27, pp.884--886 and 934--935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06
open Section03.A5Setup Section03.SourceCompletion
open Section05.A5Source CentralizerReduction CentralizerReduction.A5Module
open TerminalContradiction TerminalContradiction.Components
open TerminalContradiction.Components.SuzukiIsolation
open Chapter12.Section02 Chapter6.Source.RankOneGeneric

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}

/-- Construct the chosen module and the invariant flag from the original
local 13.3.2 clause. No universal module record or Context is assumed. -/
theorem exists_context_of_original_A5_modules_at
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodules : OriginalAlternatingFiveModules1332At T L) :
    ∃ V V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧ Nonempty (Context T L V V₁ V₂ V₃) := by
  obtain ⟨V, ⟨D⟩⟩ := (OriginalMaximality.hypothesis1221 h e).exists_chosen_of_normalizes hn
  have hmodel := hmodules h L h.local_component ⟨e⟩ V D
  obtain ⟨V₁, V₂, V₃, h23, hd⟩ := exists_context_of_one_or_two_modules h D (Or.inl hmodel)
  exact ⟨V, V₁, V₂, V₃, h23, hd⟩

/-- The complete local A₅ application to the residual split. The two
exceptional models are handled before requesting their counterexample-only
centralizer and recognition inputs. -/
theorem source_qtkeModel_of_original_A5_sources_at
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h12213 : Theorem12213At KnownSimple.IsKnownSimple T)
    (hCv : IsA5Counterexample G → ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (hescape : IsA5Counterexample G →
      ∀ (V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      Context T L V V₁ V₂ V₃ →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        H ≤ centralizer (V₁ : Set G) → 1 < ChapterE.generationParameter H →
        ¬ Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* L3Four) →
        ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
          normalizer ((pResidual 2 H).map H.subtype : Set G) →
        Source523.LocalAlternative T L H V 2)
    (hunique : IsA5Counterexample G → ∀ X : Subgroup G,
      IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G))
    (hrecognize : IsA5Counterexample G →
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
      RankOneModule.GlobalExit G) : ClassificationModels.IsQTKEModel G := by
  classical
  by_cases hu : ClassicalGroup.IsPSU G 4 2
  · exact (ClassificationModels.IsTheoremDExceptionalModel.unitary_binary hu).toQTKEModel
  by_cases hl : ClassicalGroup.IsPSL G 4 3
  · exact (ClassificationModels.IsTheoremDExceptionalModel.linear_three hl).toQTKEModel
  have hc : IsA5Counterexample G := ⟨hu, hl⟩
  obtain ⟨V, V₁, V₂, V₃, h23, ⟨d⟩⟩ :=
    exists_context_of_original_A5_modules_at h e hn hmodules
  have hv := hCv hc V V₁ V₂ V₃ h23 d
  exact source_qtkeModel_of_original_rankOne_sources_at d hmany hv
    (singular_escape_of_source12213_at d hv h12213) hc
    (hescape hc V V₁ V₂ V₃ h23 d) (hunique hc)
    (hrecognize hc V V₁ V₂ V₃ h23 d)

end CFSG.Quasithin.Chapter13.Section06
