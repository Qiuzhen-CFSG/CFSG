module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.Replacement

/-!
# The original noncentrality contradiction for the six-point replacement

The replacement belongs to the literal Y_z family, so original 13.6.17
applies to the same earlier conjugate a, without another reduced-model
hypothesis for the replacement. This packages precisely the contradiction
needed after its six-point fixed-space calculation.

Source: Aschbacher–Smith, 13.6.17 and 13.6.22, printed pp.930–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open ComponentSelection A5Module SourceContainment ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- No member of the actual source family centralizes its marked conjugate a.
This applies to the constructed replacement directly, before any new block
classification or model catalogue is invoked on that subgroup. -/
theorem selected_not_centralizes_markedA_original_source
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
    (B : Subgroup G)
    (hB : B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    ¬ B ≤ Gv (markedA d.flag.module) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 B hB hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g, hg⟩ := c.a_conjugate
    exact ⟨g, c.aPoint_val.trans hg.symm⟩
  simpa only [c.aPoint_val, Gv] using hnc hconj c.a_checked_central

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
