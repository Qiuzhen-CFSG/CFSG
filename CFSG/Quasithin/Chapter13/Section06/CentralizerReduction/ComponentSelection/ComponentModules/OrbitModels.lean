module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue.Adequate
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Models.Intersection

/-!
# The FF catalogue on the original two-orbit component

The original plus component lies in the offender subgroup because the whole
T_v-orbit does. Restriction preserves its subnormality and quasisimplicity.
Apply the proved adequate B.5.6 classification to that literal offender
action, then extract its actual component model and divisibility by three.
The adequate outer case uses only the A₆–C₃ group shape.

This is the B.5.6 side of the comparison with 1.2.1(3) in the first sentence
of 13.6.14. No component-invariance, module model, or classification premise
is added to the source hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929; B.5.6, printed p.105.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual K⁺ is an ordinary component in the original offender actor,
before any T_v-invariance assertion for K. -/
theorem orbit_plus_component_source (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) (hK : K ∈ Yz L T z v) :
    IsComponent (offenderSubgroup (wkRepresentation K L T z v hL hz))
      ((plusImage K L T z v hL hz K).subgroupOf
        (offenderSubgroup (wkRepresentation K L T z v hL hz))) := by
  have hCI : plusImage K L T z v hL hz K ≤
      offenderSubgroup (wkRepresentation K L T z v hL hz) :=
    (map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans
      (orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK)
  exact (show IsComponent (Gplus K L T z v hL hz)
    (plusImage K L T z v hL hz K) from
      ⟨plusImage_K_subnormal K L T z v hL hz hK,
        plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩).subgroupOf hCI

/-- The full FF model catalogue and the three-divisibility conclusion on
the same literal K⁺ used by the original W_K action. -/
theorem orbit_plus_ff_model_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) :
    QuasisimpleModel (plusImage K L T z v hL hz K) ∧
      3 ∣ Nat.card (plusImage K L T z v hL hz K) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  let ρ := wkRepresentation K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let I := offenderSubgroup ρ
  have hzT := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzOmega).1
  have hCI : C ≤ I :=
    (map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans
      (orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK)
  have hm := component_model_of_native_alternative (ρ.comp I.subtype)
    (orbit_adequateAlternative_source hG K L T z v hv hL hz hSylow hzOmega hf hK)
    (orbit_plus_component_source K L T z v hL hz hzT hSylow hK)
  have hmodel : QuasisimpleModel C :=
    quasisimpleModel_of_equiv (subgroupOfEquivOfLe hCI).symm hm
  let : IsQuasisimple C := plusImage_K_quasisimple_source K L T z v hL hz hK hSylow
  exact ⟨hmodel, three_dvd_card_of_quasisimpleModel hmodel⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original 13.6 setup supplies every applicability premise of the
actual component model comparison, including characteristic two. -/
theorem orbit_plus_ff_model_original_source
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
    QuasisimpleModel (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K) ∧
      3 ∣ Nat.card (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact orbit_plus_ff_model_source hG K L (T : Subgroup G) _ _
    (marked_orders d.flag.module).2 hL hz
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ (markedZ_mem_Tv_omega d)
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion) hK

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
