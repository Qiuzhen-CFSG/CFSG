module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualImage
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NineInverter

/-!
# The full elementary-nine image and its original core inverter

In the order-nine branch of the Omega row, the literal image of
`Y = O²(⟨Rc^M⟩)` is the entire odd residual of the actor S₃ × S₃.
It has actual C₃ × C₃ coordinates. Full movement by the intersection-core
image supplies an involution inverting both cubic factors; lifting its
membership through the range-restricted action gives an element of the
original Rc, with its specified action on the literal image of Y.

These are the actor inputs for the central extension above Y-bar. They do
not identify Y-star with its image or assume the resulting classification.

Source: Aschbacher--Smith, 15.2.3(1), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The order-nine branch is the full residual of the actual action image. -/
theorem source_omega_nine_image_eq_residual (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict = pResidual 2 (actionHom M V hn).range := by
  rw [source_omega_caseIIResidual_image_commutator T hTM hTMc hn ho] at hc ⊢
  exact SymmetricThreeProductResidual.commutator_eq_residual_of_card_nine
    (D := (actionHom M V hn).range) ho.2.2.2.1.some _ hc

/-- The actual order-nine residual image has elementary-nine coordinates. -/
theorem source_omega_nine_image_equiv (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    Nonempty ((((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  obtain ⟨e⟩ := SymmetricThreeProductResidual.residual_equiv_elementaryNine
    (X := (actionHom M V hn).range) ho.2.2.2.1.some
  exact ⟨(MulEquiv.subgroupCongr
    (source_omega_nine_image_eq_residual T hTM hTMc hn ho hc)).trans e⟩

/-- An element of the original intersection core induces an involution
inverting the full order-nine image of the original Y. -/
theorem source_omega_nine_image_inverter (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    let f := (actionHom M V hn).rangeRestrict
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M
    ∃ r : M, r ∈ ((M ⊓ Mc).pCoreIn 2).subgroupOf M ∧ orderOf (f r) = 2 ∧
      ∀ y ∈ Y.map f, f r * y * (f r)⁻¹ = y⁻¹ := by
  let f := (actionHom M V hn).rangeRestrict
  let P := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  have hle : R ≤ (P : Subgroup (actionHom M V hn).range) :=
    map_mono (comap_mono hRT)
  have hfull : ⁅pResidual 2 (actionHom M V hn).range,R⁆ =
      pResidual 2 (actionHom M V hn).range := by
    rw [← source_omega_caseIIResidual_image_commutator T hTM hTMc hn ho]
    exact source_omega_nine_image_eq_residual T hTM hTMc hn ho hc
  obtain ⟨r',hr',hr2,hi⟩ := SymmetricThreeProductResidual.exists_full_residual_inverter
    (X := (actionHom M V hn).range) ho.2.2.2.1.some P R hle hfull
  obtain ⟨r,hr,he⟩ := hr'
  subst r'
  refine ⟨r,hr,hr2,fun y hy => hi y ?_⟩
  rwa [← source_omega_nine_image_eq_residual T hTM hTMc hn ho hc]

/-- The inverter in the exact nonidentity-and-square form used to lift it
through the local two-core quotient. -/
theorem source_omega_nine_inverter (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    let f := (actionHom M V hn).rangeRestrict
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M
    ∃ r : M, r ∈ ((M ⊓ Mc).pCoreIn 2).subgroupOf M ∧ f r ≠ 1 ∧ (f r) ^ 2 = 1 ∧
      ∀ y ∈ Y.map f, f r * y * (f r)⁻¹ = y⁻¹ := by
  obtain ⟨r,hr,ho,hi⟩ := source_omega_nine_image_inverter T hTM hTMc hn ho hc
  have hp := orderOf_eq_prime_iff.mp ho
  exact ⟨r,hr,hp.2,hp.1,hi⟩

end CFSG.Quasithin.Chapter15.Section02
