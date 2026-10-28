module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.SourceNormalized
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSixSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reduction

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open A5Module ComponentReduction InitialSieve NormalizedBorel
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The complete 13.6.6 characteristic-two conclusion. Every component is
split into the source-normalized and source-moving cases. The normalized case
uses the actual signed-three/root and Sp4 Borel contradiction; the moving case
uses the independent original PSL2/Suzuki pair construction. -/
theorem generalizedFitting_eq_pCore_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module) :
    generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)) := by
  by_contra hnot
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  obtain ⟨K, hK, _a, _ha⟩ :=
    initial_component_of_earlier_source d V₃ earlier hG
      (hm.V_le_core.trans (map_subtype_le _)) hcounter hfusion hnot
  have hTN := MovingComponent.Tv_normalizes_component_of_earlier_source
    d V₃ earlier hG hm hcounter hfusion K hK
  have hTNlocal : localT (T : Subgroup G) (markedV d.flag.module) ≤ X K := by
    have hsub := Subgroup.subgroupOf_mono (Gv (markedV d.flag.module)) hTN
    rw [subgroupOf_normalizer_eq (map_subtype_le K)] at hsub
    have hkmap : ((map (Gv (markedV d.flag.module)).subtype K).subgroupOf
        (Gv (markedV d.flag.module))) = K := by
      rw [subgroupOf, comap_map_eq_self_of_injective
        (Gv (markedV d.flag.module)).subtype_injective]
    have hTv : (Tv (T : Subgroup G) (markedV d.flag.module)).subgroupOf
        (Gv (markedV d.flag.module)) =
        localT (T : Subgroup G) (markedV d.flag.module) := by
      rw [Tv, inf_comm, inf_subgroupOf_left]
      rfl
    rw [hkmap] at hsub
    rw [hTv] at hsub
    exact hsub
  exact (normalized_component_false_of_earlier_source d V₃ earlier hG hm
    hcounter hfusion K hK hTNlocal).elim

/-- The genuine 13.6.8--9 consumer on the same source configuration.  The
characteristic-two equality is supplied by the preceding theorem, while the
failure of normality remains the actual counterexample hypothesis used by the
geometric Thompson reduction. -/
theorem geometric_reduction_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : ComponentSelection.FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G)) :
    ComponentSelection.GeometricThompsonReduction L (T : Subgroup G)
      (normalizer (L : Set G)) (markedZ d.flag.module) (markedV d.flag.module) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact ComponentSelection.geometric_thompson_reduction_of_localReductions d.flag
    c.reductions hform
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion)
    hfailure

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
