module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSevenOriginal.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource

/-!
# Original exceptional-A₇ exclusion in 13.6.22

The original local configuration and the completed 13.6.20 containment
construct the source moving plane and its full residual actor on the
exceptional four-space. The actor catalogue and checked Sylow averaging
force K to centralize the exact earlier conjugate a. Original 13.6.17
contradicts this centralization.

No representation, actor, seed-in-K, core-intersection or supplement premise
remains. The genuine earlier flag/local, fusion/form, failed-normalization,
reduced-catalogue and universal 13.3.2/13.6.3 inputs are retained with the
same maps and conventions as the other original small-model exclusions.

Source: Aschbacher–Smith, 13.6.17 and 13.6.20–22, printed pp.930–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original source configuration excludes the exceptional-A₇ block,
including its noncyclic permitted residual actors. -/
theorem not_exceptionalSeven_original_source
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
    ¬ IsExceptionalA7Block K := by
  intro h
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  have hc := exceptionalSeven_centralizes_markedA_of_localConfiguration d c h hK hn hLK hchar
    earlier.T_normalizes_L
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g, hg⟩ := c.a_conjugate
    exact ⟨g, c.aPoint_val.trans hg.symm⟩
  apply hnc hconj c.a_checked_central
  simpa only [c.aPoint_val, Gv] using hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
