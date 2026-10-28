module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.Source13614
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.NaturalConsumer
/-!
# Applying component invariance to the original seed and natural action

The proved 13.6.14 supplies T_v-invariance in the original 13.6.15 seed
exclusion and in the natural-action consumer used in 13.6.18. Every statement
keeps the same W_K instance, plus map, marked seed and chosen finite field.
Source: Aschbacher--Smith 13.6.14--15,18, printed pp.929--931.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module ComponentReduction InitialSieve ChapterB.QuasisimpleSource
open ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

section
variable (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G))
include d V₃ earlier hG hm hcounter hfusion hform hfailure K hK hL hz

theorem alternating_seed_excluded_original_source :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    ExcludesAlternatingFiveSeed K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz :=
  AlternatingSeed.excludes_alternatingFiveSeed_original_source d V₃ earlier hG hm hcounter hfusion
    hform hfailure K hK (component_invariant_original_source d V₃ earlier hG hm hcounter hfusion K hK) hL hz

theorem natural_action_original_source (F : BinaryField)
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
      Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    Nonempty (ActionEquiv (ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action.sectionRepresentation
      K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz) (linearNatural F 2)) :=
  AlternatingSeed.natural_actionEquiv_original_source d V₃ earlier hG hm hcounter hfusion
    hform hfailure K hK (component_invariant_original_source d V₃ earlier hG hm hcounter hfusion K hK) hL hz F e
end
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
