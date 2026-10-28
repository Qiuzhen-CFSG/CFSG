module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.ProductRows
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitModels

/-!
# The original component catalogue before the field exclusions

Apply the complete native B.5 classification to the original offender action
on W_K. The actual plus component remains a component in that actor, so the
group catalogue applies to that same image. No model-classification
premise remains. The subsequent field exclusions apply this catalogue
in `ReducedSource`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph before 13.6.20, printed p.931.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete component catalogue on the original W_K action quotient. -/
theorem model_source (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) : Model (plusImage K L T z v hL hz K) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  let ρ := wkRepresentation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let I := offenderSubgroup ρ
  have hzT := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzOmega).1
  have hCI : C ≤ I :=
    (map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans
      (orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK)
  have hm := model_of_adequate_alternative
    (orbit_adequateAlternative_source hG K L T z v hv hL hz hSylow hzOmega hf hK)
    (orbit_plus_component_source K L T z v hL hz hzT hSylow hK)
  exact Model.transport (subgroupOfEquivOfLe hCI) hm

variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original marked local configuration supplies the entire catalogue. -/
theorem model_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    Model (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact model_source hG K L (T : Subgroup G) _ _
    (marked_orders d.flag.module).2 hL hz
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩ (markedZ_mem_Tv_omega d)
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion) hK

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
