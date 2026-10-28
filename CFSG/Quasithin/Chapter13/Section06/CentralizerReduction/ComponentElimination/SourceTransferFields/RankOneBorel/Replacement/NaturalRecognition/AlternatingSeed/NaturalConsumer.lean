module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Source
/-!
# The original natural-action consumer of 13.6.15

The same FlagSource configuration now supplies the alternating-five seed
exclusion internally. The existing full known-simple classifier therefore
returns natural coordinates on the literal U_K/C_U_K(K) action over the
specified field, with no remaining seed-exclusion premise.
Source: Aschbacher–Smith, first paragraph of 13.6.18, printed p.931.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection A5Module ComponentReduction InitialSieve ChapterB.QuasisimpleSource
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
theorem natural_actionEquiv_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G))
    (F : BinaryField)
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
      Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    Nonempty (ActionEquiv (Replacement.Action.sectionRepresentation K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz) (linearNatural F 2)) := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  dsimp only
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃ earlier hcounter hfusion
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion
  have hex := excludes_alternatingFiveSeed_original_source d V₃ earlier hG hm hcounter hfusion
    hform hfailure K hK hn hL hz
  exact CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Source.natural_actionEquiv (hG := hG) (K := K) (L := L) (T := (T : Subgroup G))
    (z := markedZ d.flag.module) (v := markedV d.flag.module) (hv := (marked_orders d.flag.module).2)
    (hL := hL) (hz := hz) (hSylow := ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩)
    (hzOmega := markedZ_mem_Tv_omega d) (hf := hf) (hK := hK) (hn := hn) (F := F) (e := e)
    (classification := ChapterB.SourceInduction.adequateClassification_knownSimple) hex
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
