module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualImage
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Movement

/-!
# The moved residual and cubic inversion in the original Omega case

The original intersection core Rc lies in the given Sylow subgroup.
Transporting the symmetric-three-square calculation through the literal
conjugation map proves Y-bar=[Y-bar,Rc-bar], and noncentrality makes this
image nontrivial. When it has order three, Rc-bar has order two and its
nonidentity element inverts Y-bar. The central extension above this image
is handled separately; no equality with Y-star is assumed here.

Source: Aschbacher--Smith, 15.2.3(1), printed pp.1104--1105.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem core_image_le_sylow {D : Type*} [Group D] (T : Sylow 2 G)
    {M Mc : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hTMc : (T : Subgroup G) ≤ Mc) (f : M →* D) (hf : Function.Surjective f) :
    (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f ≤
      ((T.subtype hTM).mapSurjective hf : Subgroup D) := by
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  exact map_mono (comap_mono hRT)

theorem source_omega_caseIIResidual_image_self_commutator (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    let f := (actionHom M V hn).rangeRestrict
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M
    let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
    ⁅Y.map f, R.map f⁆ = Y.map f := by
  let f := (actionHom M V hn).rangeRestrict
  let P := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hle := core_image_le_sylow T hTM hTMc f (actionHom M V hn).rangeRestrict_surjective
  have hh := SymmetricThreeProductResidual.residual_self_commutator
    (D := (actionHom M V hn).range)
    ho.2.2.2.1.some P ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f) hle
  dsimp only at hh
  rw [SymmetricThreeProductResidual.normalClosure_residual_eq_commutator
    (D := (actionHom M V hn).range)
    ho.2.2.2.1.some P _ hle] at hh
  dsimp only
  rw [source_omega_caseIIResidual_image_commutator T hTM hTMc hn ho]
  exact hh

theorem source_omega_residual_image_movement (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    let f := (actionHom M V hn).rangeRestrict
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M
    let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
    Y.map f ≠ ⊥ ∧ ⁅Y.map f, R.map f⁆ = Y.map f := by
  refine ⟨?_,source_omega_caseIIResidual_image_self_commutator T hTM hTMc hn ho⟩
  intro he
  have hc := source_omega_caseIIResidual_image_order T hTM hn ho hRc
  rw [he,card_bot] at hc
  omega

theorem source_omega_cubic_image_inversion (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 3) :
    let f := (actionHom M V hn).rangeRestrict
    let Y := (caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M
    let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
    Nat.card (R.map f) = 2 ∧ ∀ r ∈ R.map f, r ≠ 1 →
      ∀ y ∈ Y.map f, r * y * r⁻¹ = y⁻¹ := by
  let f := (actionHom M V hn).rangeRestrict
  let P := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hle := core_image_le_sylow T hTM hTMc f (actionHom M V hn).rangeRestrict_surjective
  rw [source_omega_caseIIResidual_image_commutator T hTM hTMc hn ho] at hc
  have hh := SymmetricThreeProductResidual.cubic_actor_inverts
    (D := (actionHom M V hn).range)
    ho.2.2.2.1.some P ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f) hle hc
  dsimp only
  rw [source_omega_caseIIResidual_image_commutator T hTM hTMc hn ho]
  exact hh
end CFSG.Quasithin.Chapter15.Section02
