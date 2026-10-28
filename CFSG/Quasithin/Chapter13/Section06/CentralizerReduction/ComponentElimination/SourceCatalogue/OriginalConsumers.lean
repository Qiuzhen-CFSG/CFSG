module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly

/-!
# Original component containment and block exclusions from the full catalogue

The actual offender classification and original field exclusions construct the
seven-model list on each selected plus component. This removes the independent
reduced-model premise from both Lᵥ containment and all the short-block
exclusions. The same original flag, component, plus quotient and local data
are retained throughout.

These are the component statements used by the rank-four centralizer endgame.
They leave the genuine earlier universal normalization and omega-centralizer
inputs explicit; quotient-to-block reconstruction remains separate.
Source: Aschbacher–Smith 13.6.20–22, printed pp.931–933.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}
variable
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))

include d V₃ earlier standing hm hfusion hform hfailure h1332 h63 hK hL hz

/-- Original 13.6.20–21 with the seven-model premise discharged by B.5. -/
theorem containment_and_noncontainment_original_source :
    Lv L (markedV d.flag.module) ≤ K ∧ ¬ K ≤ normalizer (L : Set G) := by
  exact SourceContainment.containment_and_noncontainment_original_source d V₃ earlier
    standing hm hfusion h1332 h63 hK hL hz
    (reduced_model_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 K hK hL hz)

/-- All original short-block exclusions use the same proved catalogue,
without an extra group-classification premise. -/
theorem small_block_exclusions_original_source :
    ¬ IsLinearTwoBlock K 3 ∧ ¬ SourceSmallModels.BinaryRankTwo.SourceBlock K ∧
      ¬ IsExceptionalAhat6Block K ∧ ¬ IsAlternatingBlock K 7 ∧ ¬ IsExceptionalA7Block K := by
  exact SourceSmallModels.small_block_exclusions_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz
    (reduced_model_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 K hK hL hz)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
