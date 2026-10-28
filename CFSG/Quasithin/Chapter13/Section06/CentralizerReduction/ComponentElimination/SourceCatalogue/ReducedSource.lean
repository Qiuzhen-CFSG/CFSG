module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.ComponentSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.OriginalSource

/-!
# The original seven-model catalogue before 13.6.20

The complete component catalogue and original 13.6.18–19 exclude every
rank-one and larger-field alternative. The seven surviving actual models
therefore require no separate catalogue premise. The earlier universal
13.3.2 normalization and 13.6.3 omega-centralizer statements remain explicit,
as in the field-exclusion theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph before 13.6.20, printed p.931.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ComponentSelection A5Module ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- Original 13.6.18–19 discharge every field alternative on the actual
selected component, leaving the exact seven models required in 13.6.20. -/
theorem reduced_model_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceContainment.RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      SourceContainment.RankTwo.LocalApplication.SourceHypothesis S I →
      Stellmacher.omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    SourceContainment.RankTwo.ReducedModel
      (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K) := by
  apply Model.reduced_of_field_exclusions
    (model_original_source d V₃ earlier standing.qtke hm standing.counterexample hfusion K hK hL hz)
  · intro F
    exact (SourceTransferFields.noncentrality_and_field_exclusions_original_source
      d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz F).2.1
  · intro F hF
    exact (SourceTransferFields.noncentrality_and_field_exclusions_original_source
      d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz F).2.2 hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
