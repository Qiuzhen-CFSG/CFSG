module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Models

/-!
# Actual nonnormal-component models in the rank-one source argument

The proved 1.2.1 catalogue applies to the selected C-component in the
original outside subgroup. Comparing it with the corrected adequate B.5
model of its literal Thompson image leaves binary PSL₂ or PSL₃(2).
No universal legacy classification or residual interface is assumed.

Source: Aschbacher–Smith 1.2.1(3) and the first paragraph of 15.3.27,
printed pp.503 and1130.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration
open Chapter1.Section02
open RankOneConfiguration.Parabolics.Placement
open RankOneConfiguration.Parabolics.Placement.OrbitBorel
variable {G : Type*} [Group G] [Finite G]

/-- The actual nonnormal catalogue and index, on the original component. -/
theorem source_component_orbit_index_and_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal) :
    (normalizer (c.L : Set G)).relIndex I = 2 ∧
      NonnormalCComponentModel (c.L ⧸ pCore 2 c.L) := by
  have hc := LocalData.thompson_component_in c.le_thompson c.component
  obtain ⟨hi, hm⟩ := (proposition_1_2_1_three_index_knownSimple
    (OutsideStructure.outside_twoCoreQuotient_sqtk hG d hI) hc).resolve_left hn
  refine ⟨?_, ?_⟩
  · rw [← subgroupOf_normalizer_eq (component_le c)] at hi
    exact hi
  · let e := (subgroupOfEquivOfLe (component_le c)).symm
    exact hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

/-- Corrected B.5 and the original 1.2.1 source give the matching intrinsic
and star quotient models used by the orbit-Borel contradiction. -/
theorem source_component_models_of_nonnormal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hn : ¬ (c.L.subgroupOf I).Normal) (hS : Chapter1.IsSylowIn 2 d.S I) :
    ComponentModelAlternatives d c := by
  have hm := (source_component_orbit_index_and_model hG d hI c hn).2
  have hstar := component_star_ff_model hG d hI hf c hS
  have hVT := d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  have hquot := ModelComparison.Catalogue.quasisimpleModel_of_equiv
    (nonnormalComponentQuotientEquivStar d c hS (d.Z_le_S hVT) hm) hstar
  let _ := c.core_quotient_quasisimple
  exact componentModelAlternatives_of_intrinsic_models d c hS (d.Z_le_S hVT) hm
    (intrinsic_model_intersection hm hquot (component_three_divides_quotient d c))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
