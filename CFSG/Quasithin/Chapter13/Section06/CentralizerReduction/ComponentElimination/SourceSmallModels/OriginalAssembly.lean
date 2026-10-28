module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSevenOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SevenExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement.Alternating

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.Catalogue

/-!
# The original small-block exclusions in 13.6.22

The original flag, local configuration and earlier source statements exclude
all five short-block alternatives: natural L₃(2), A₆ or G₂(2)′, covered A₆,
ordinary A₇ and exceptional A₇. Each branch constructs its actual action and
applies original 13.6.17 to the marked conjugate. The ordinary A₇ branch uses
the constructed six-point replacement, with no extra block premise for it.

The A₇ quotient-to-block step is now proved from the original hypotheses.
The complete B.5 action classification, both C.1.24 local seeds and the
original characteristic-Baumann obstruction construct the actual ordinary
or exceptional block. Their exclusions remove the A₇ constructor from the
plus quotient catalogue. The literal minimal same-star replacement is also
available with its action marking preserved.

The C132 extensions construct every original MS hypothesis and compare
all five C.1.32 outcomes with the actual nonlinear small central quotients.
Together with prescribed MS path replacement, their conditional assembly
now gives the literal SL₄/SL₅ catalogue and nonsingular centralizer bound.
The universal small C.1.32 implication and prescribed replacement remain
independent source obligations; full C.1.34 exhaustiveness is not required.

Source: Aschbacher–Smith, 13.6.22, printed pp.932–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open ComponentSelection A5Module SourceContainment ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- All source short-block branches of 13.6.22 are impossible under the
same original hypotheses. Quotient-to-block selection is not an assumption
of an individual exclusion and is not asserted by this conjunction. -/
theorem small_block_exclusions_original_source
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
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    ¬ IsLinearTwoBlock K 3 ∧ ¬ BinaryRankTwo.SourceBlock K ∧
      ¬ IsExceptionalAhat6Block K ∧ ¬ IsAlternatingBlock K 7 ∧ ¬ IsExceptionalA7Block K := by
  obtain ⟨hb, hc⟩ := not_binary_or_coveredSix_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz model
  exact ⟨LinearThreeBranch.not_linearTwoBlock_original_source d V₃ earlier standing hm
      hfusion hform hfailure h1332 h63 hK hL hz model,
    hb, hc, not_ordinarySeven_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 hK hL hz model,
    not_exceptionalSeven_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 hK hL hz model⟩

/-- Apply the established exclusions to every actual selected component.
The source's reduced-model catalogue remains the same earlier universal
input used by containment and rank-four selection. -/
theorem all_selected_small_block_exclusions_original_source
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
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (models : ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      RankTwo.ReducedModel (plusImage B L (T : Subgroup G)
        (markedZ d.flag.module) (markedV d.flag.module) hL hz B)) :
    ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      ¬ IsLinearTwoBlock B 3 ∧ ¬ BinaryRankTwo.SourceBlock B ∧
        ¬ IsExceptionalAhat6Block B ∧ ¬ IsAlternatingBlock B 7 ∧ ¬ IsExceptionalA7Block B := by
  intro B hB
  exact small_block_exclusions_original_source d V₃ earlier standing hm hfusion hform hfailure
    h1332 h63 hB hL hz (models B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
