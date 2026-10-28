module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.NoncentralLift

/-!
# Source assembly up to ambient component normalization

The marked A₅ configuration and full Hypothesis 13.3.1 feed the completed
central-action argument. The nonzero plus commutator supplies the actual
projection, its Sylow marking and parabolic residual recognition. The
cubic quotient of Lᵥ is obtained from the marked local configuration.

The containment lift consumes one additional hypothesis, that Lᵥ normalizes
the original K. This is not one of the earlier source conclusions proved
by this module. The enclosing 13.6.20 owner must discharge it before
claiming the source containment theorem. No full plus-kernel bound,
centralizer-absorption premise or assumed projection identity is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.20, printed p.931; marked local configuration, pp.926–930.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection A5Module
universe u
variable {G : Type u} [Group G] [Finite G]
    {K L M V V₁ V₂ : Subgroup G} {T : Sylow 2 G}

/-- Conditional assembly of the L₃(2) branch: all module and parabolic
premises are discharged, while normalization of the original K by L_v
remains an explicit, separate source obligation. -/
theorem lv_le_and_noncentral_of_source_of_normalizes
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hM : M = normalizer (L : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV f.module)) =
      pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))⁆)
    (hL : Tv (T : Subgroup G) (markedV f.module) ≤
      normalizer (Lv L (markedV f.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV f.module) ≤
      centralizer ({markedZ f.module} : Set G))
    (model : plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
      hL hz K ≃* Matrix.PSL3Two.PSL)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hLK : Lv L (markedV f.module) ≤ normalizer (K : Set G)) :
    Lv L (markedV f.module) ≤ K ∧
    ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module) hL hz K,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        hL hz (Lv L (markedV f.module))⁆ ≠ ⊥ := by
  have hcomm := CentralAction.plus_commutator_ne_bot_of_source standing f c hM hTL hK hn
    hchar hgen hL hz model earlier classification
  exact ⟨lv_le_of_noncentral_of_normalizes K L (T : Subgroup G) (markedZ f.module)
    (markedV f.module) hL hz hK hn model c.residual_card hcomm hLK, hcomm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
