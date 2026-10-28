module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Source
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ReducedSource
/-!
# Original 13.6.15 on the constructed FlagSource configuration

The earlier configuration supplies the centralizer Sylow and cubic residual
quotient. The proved 13.6.6–9 reduction supplies characteristic two and the
elementary modules; the original flag supplies the central seed. These facts
instantiate the complete seed exclusion on the same K,L,T,z,v and plus action.
Only the separately owned 13.6.14 normalization of K remains explicit.
Source: Aschbacher–Smith, 13.6.15, printed p.930 (PDF p.947).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
theorem excludes_alternatingFiveSeed_original_source
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
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G)) :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    ExcludesAlternatingFiveSeed K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  dsimp only
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃ earlier hcounter hfusion
  have r := geometric_reduction_of_earlier_source d V₃ earlier hG hm hcounter hfusion hform hfailure
  let := r.module_reduced.2.1
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion
  exact excludes_alternatingFiveSeed_source hG d.flag.module K (T : Subgroup G) hL hz
    c.reductions.centralizerSylow c.reductions.sylow_image (markedZ_mem_Tv_omega d) hf hK hn c.residual_card
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
