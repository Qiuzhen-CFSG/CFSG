module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Preparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# B.5.6 on the component orbit before 13.6.14

Membership in Y_z gives the Thompson commutator identity for the entire
T_v-orbit K₋, even when K is not invariant. Transport that identity through
the actual star-to-plus map. The orbit is normal in the plus actor and lies
in its subgroup of best offenders. This supplies the complete B.5.3
hypotheses and the proved adequate B.5.6 alternatives for the literal W_K
action before invoking the invariance assertion of 13.6.14.

Source: Aschbacher--Smith, paragraph before 13.6.14, printed p.929.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The entire orbit image is normal without assuming K invariant. -/
theorem plusImage_Kminus_normal_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v) :
    (plusImage K L T z v hL hz (Kminus K T v)).Normal := by
  have h := starImage_Kminus_normal_in_actor K L T z v hK
  have hm := h.map (starToPlus K L T z v hK.1.1 hL hz)
    (starToPlus_surjective K L T z v hK.1.1 hL hz)
  rwa [starToPlus_image K L T z v hK.1.1 hL hz (Kminus K T v)
    (le_sup_left.trans le_sup_left)] at hm

omit [Finite G] in
/-- The defining X_z commutator survives the actual plus quotient. -/
theorem orbit_plus_commutator_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v) :
    ⁅plusImage K L T z v hL hz (Kminus K T v),
      plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))⁆ =
        plusImage K L T z v hL hz (Kminus K T v) := by
  let A := starImage z v (plusActor K L T v)
  let C := starImage z v (Kminus K T v)
  let J := starImage z v (elementaryAbelianMaxJ (Tv T v))
  have hJA : elementaryAbelianMaxJ (Tv T v) ≤ plusActor K L T v :=
    (sSup_le fun _ h => h.1).trans le_sup_right
  have hCA : C ≤ A := map_mono (comap_mono (le_sup_left.trans le_sup_left))
  have hJAs : J ≤ A := map_mono (comap_mono hJA)
  have hc : ⁅C, J⁆ = C := by
    have h := hK.2.2.1.2.2.2
    rwa [← starImage_Kminus K T z v hK.1.1] at h
  have hr : ⁅C.subgroupOf A, J.subgroupOf A⁆ = C.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCA,
      map_subgroupOf_eq_of_le hJAs, hc]
  have hm := congrArg (map (starToPlus K L T z v hK.1.1 hL hz)) hr
  rw [map_commutator] at hm
  simpa only [C, J, A,
    starToPlus_image K L T z v hK.1.1 hL hz (Kminus K T v) (le_sup_left.trans le_sup_left),
    starToPlus_image K L T z v hK.1.1 hL hz (elementaryAbelianMaxJ (Tv T v)) hJA] using hm

/-- Every orbit factor is retained inside the actual classifier actor. -/
theorem orbit_plus_le_offenders_source (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) (hK : K ∈ Yz L T z v) :
    plusImage K L T z v hL hz (Kminus K T v) ≤
      offenderSubgroup (wkRepresentation K L T z v hL hz) := by
  let ρ := wkRepresentation K L T z v hL hz
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  rw [← orbit_plus_commutator_source K L T z v hL hz hK]
  exact (commutator_mono le_rfl
    (thompson_plus_le_offenders K L T z v hK.1.1 hL hz hzT hSylow)).trans
      (commutator_le_right _ _)

/-- The orbit supplies all source applicability fields before invariance. -/
theorem orbit_classifierApplicability_source {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz (Kminus K T v)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  exact ⟨Module.Finite.of_finite, wkRepresentation_faithful K L T z v hL hz,
    plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow,
    plusImage_Kminus_normal_source K L T z v hL hz hK,
    orbit_plus_le_offenders_source K L T z v hL hz
      ((mem_omegaOneCenterAmbient_iff _ _).mp hzOmega).1 hSylow hK,
    plus_sqtk_quotient hG K L T z v hv hK.1.1 hL hz⟩

/-- The proved complete classifier applies to the original W_K action
restricted to its best offenders, with no universal classification premise. -/
theorem orbit_adequateAlternative_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    let ρ := wkRepresentation K L T z v hL hz
    ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  exact ChapterB.SourceInduction.adequateAlternative_knownSimple _
    (Classifier.offender_hypothesis
      (orbit_classifierApplicability_source hG K L T z v hv hL hz hSylow hzOmega hf hK))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
