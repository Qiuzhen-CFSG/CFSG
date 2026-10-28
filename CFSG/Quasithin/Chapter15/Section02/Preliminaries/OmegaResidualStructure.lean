module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualMovement
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCyclicExtension

/-!
# Original Omega residual alternatives

This assembles the movement and cyclic-kernel arguments on the same original
Y and Rc. A noncentral intersection core gives a nontrivial moved image.
For a cubic image, the literal star image also has order three, its module
centralizer is its two-core, and the order-two core image acts by inversion.
For the full order-nine image, the earlier source argument supplies uniqueness
of the maximal two-local overgroup of YT.

The source's Sylow-three product in the cubic row and its order-nine
central-extension alternatives are subsequent obligations.
Source: Aschbacher--Smith, 15.2.3(1),(3), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylow_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    (T : Subgroup G) ≤ Mc := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  intro t ht
  apply hMc.2
  intro z hz
  exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm

/-- Cubic structure on the same original residual and both literal images. -/
theorem source_omega_cubic_residual_structure (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let f := (actionHom M V hV.normalized).rangeRestrict
    let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
    Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧
      Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 3 ∧
      Nat.card R = 2 ∧ ∀ r ∈ R, r ≠ 1 →
        ∀ y ∈ (Y.subgroupOf M).map f, r * y * r⁻¹ = y⁻¹ := by
  refine ⟨source_omega_cyclic_kernel_eq_core T hTM hu hV ho hcard,
    source_omega_cyclic_star_card T hTM hu hV ho hcard, ?_⟩
  exact source_omega_cubic_image_inversion T hTM (sylow_le_partner T hu)
    hV.normalized ho hcard

/-- The source Omega row has a faithful cubic residual, or the full-image
uniqueness branch. The original noncentrality premise is retained. -/
theorem source_omega_residual_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let f := (actionHom M V hV.normalized).rangeRestrict
    let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
    (Y.subgroupOf M).map f ≠ ⊥ ∧
      ⁅(Y.subgroupOf M).map f, R⁆ = (Y.subgroupOf M).map f ∧
      ((Nat.card ((Y.subgroupOf M).map f) = 3 ∧
          Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧
          Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 3 ∧
          Nat.card R = 2 ∧ ∀ r ∈ R, r ≠ 1 →
            ∀ y ∈ (Y.subgroupOf M).map f, r * y * r⁻¹ = y⁻¹) ∨
        (Nat.card ((Y.subgroupOf M).map f) = 9 ∧
          maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M})) := by
  have hm := source_omega_residual_image_movement T hM.1.2 (sylow_le_partner T hu)
    hV.normalized ho hRc
  refine ⟨hm.1,hm.2,?_⟩
  rcases source_omega_residual_branches hG T hempty hM hJ hV ho hRc with hc | hc
  · exact Or.inl ⟨hc,source_omega_cubic_residual_structure T hM.1.2 hu hV ho hc⟩
  · exact Or.inr hc
end CFSG.Quasithin.Chapter15.Section02
