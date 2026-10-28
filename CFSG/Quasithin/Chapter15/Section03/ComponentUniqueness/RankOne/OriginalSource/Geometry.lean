module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction

/-!
# The original plane reduction from inner action

The full earlier local theorem selects the genuine second residual choice
and both definite planes. Inner action then constructs the component
projection, containment, normality and every quotient-locality clause.
The broader classification alternatives are not required by this consumer.

Source: Aschbacher--Smith 15.3.43(a)--(e), printed pp.1139--1140.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The exact earlier local and definite-plane geometry, before inner action. -/
theorem original_local_geometry (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    DiagonalExclusion.LocalSetup d.Yplus d.S d.M I L ∧
      DiagonalExclusion.PlaneData d.Yplus d.S d.M I d.V₁ d.V₂ := by
  have htheta := h.outside_structure.theta_eq.symm
  have hne : d.Yplus ≠ ⊥ := by
    intro he
    apply h.outside_structure.action_normalizer.2.2
    simp [CharacteristicTwo.LocalData.starImage, localActionImage, he]
  have h11 := preliminary_alternative_of_source d h.outside_structure.local_structure
  obtain ⟨hchoice, hres, hindex⟩ :=
    rank_one_choice_of_preliminary_alternative hshadow htheta hne h11
  have hij : (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
    decide
  obtain ⟨hV₁S, hV₂S, helem, hcard, hcentral, hcomm, _, hMV₂, hA4⟩ :=
    PlaneGeometry.plane_reduction_of_preliminary_alternative d.action d.T d.sylow_le
      (localModule_le d.T d.sylow_le) h.characteristic_two h.residual_image
      h.residual_core h.residual_quotient h.not_alternating_square hij
      hshadow htheta hne h11
  obtain ⟨_, hNV₁, hNV₂, _⟩ := h.outside_structure.second_choice hchoice
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  let localSetup : DiagonalExclusion.LocalSetup d.Yplus d.S d.M I L := {
    outside := hI
    sylow := h.outside_structure.sylow
    sylow_le := hSM
    component_le := h.component_le
    component := h.component
    component_outside := h.component_outside
    odd_core := h.outside_structure.odd_core
    orbit_bound := h.component_orbit
    theta_eq := htheta
    normalizer_eq := h.outside_structure.normalizer_eq
    local_fitting := h.outside_structure.generalized_fitting
    rank_positive := h.component_rank
    rank_overgroup := h.overgroup_rank
    characteristic_two_containment := h.invariant_subgroup
    shadow := hshadow
    residual := hres
    index := hindex }
  let planes : DiagonalExclusion.PlaneData d.Yplus d.S d.M I d.V₁ d.V₂ := {
    first_le := hV₁S
    second_le := hV₂S
    first_centralizes := hcentral
    first_normalizer := hNV₁
    second_normalizer := hNV₂
    second_elementary := helem
    second_card := hcard
    second_commutator := hcomm
    second_normalized := hMV₂
    not_alternating_four := hA4 }
  exact ⟨localSetup, planes⟩

/-- Inner action suffices for the literal15.3.43 reduction; no full
classification-alternatives assertion is needed by this consumer. -/
theorem reducedConfiguration_of_original_inner (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (hi : d.Yplus ≤ L ⊔ centralizer (L : Set G)) :
    ReducedConfiguration d.Yplus d.S d.M I L d.V₁ d.V₂ := by
  obtain ⟨localSetup, planes⟩ := original_local_geometry d hI.1 h hshadow
  have hinner : ∀ y ∈ d.Yplus, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G) := by
    intro y hy
    have hm : y ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
        (Subgroup.centralizer_le_normalizer _)]
      exact hi hy
    obtain ⟨l, hl, c, hc, rfl⟩ := hm
    refine ⟨l, hl, ?_⟩
    rw [inv_mul_cancel_left]
    exact hc
  obtain ⟨P, hP⟩ := localSetup.sylow
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    (le_inf localSetup.sylow_le localSetup.sylow_le_overgroup).trans localSetup.local_normalizes
  obtain ⟨_, hYL, hgen, hnorm, _⟩ :=
    ComponentProjection.containment_and_relative_normality hI P hP h.component_le
      h.component h.component_outside hSY localSetup.theta_eq localSetup.normalizer_eq
      localSetup.residual localSetup.index h.component_center hinner
  let a : ComponentAction I L := ⟨h.component_le, hnorm⟩
  have hquot := (a.quotientConditions_of_plane hI P hP localSetup.sylow_le h.component
    h.component_center h.component_outside hYL localSetup.theta_eq localSetup.residual hshadow
    localSetup.local_fitting planes.second_le planes.second_elementary planes.second_card
    planes.second_normalized planes.second_normalizer planes.second_commutator
    h.outside_not_characteristic_two).1
  exact {
    toComponentAction := a
    minimal := hI
    sylow := ⟨P, hP⟩
    sylow_le_M := localSetup.sylow_le
    component := h.component
    oddCore := h.outside_structure.odd_core
    component_center := h.component_center
    component_outside := h.component_outside
    generated := hgen
    y_le_component := hYL
    residual := localSetup.residual
    index := localSetup.index
    theta_eq := localSetup.theta_eq
    normalizer_eq := localSetup.normalizer_eq
    local_fitting := localSetup.local_fitting
    shadow := hshadow
    plane_one_le := planes.first_le
    plane_two_le := planes.second_le
    plane_one_centralizes := planes.first_centralizes
    plane_one_acts := (plane_action_and_distinct_centralizers
      planes.first_le planes.first_centralizes planes.first_normalizer h.component_outside).1
    plane_two_elementary := planes.second_elementary
    plane_two_card := planes.second_card
    plane_two_commutator := planes.second_commutator
    plane_two_normalized := planes.second_normalized
    not_alternating_four := planes.not_alternating_four
    quotient := hquot }

end CFSG.Quasithin.Chapter15.Section03.RankOne
