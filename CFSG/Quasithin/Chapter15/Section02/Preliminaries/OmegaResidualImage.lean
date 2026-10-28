module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidual
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NormalClosure

/-!
# The three-or-nine image dichotomy for the original Omega residual

The actual image of Rc=O₂(M∩M_c) is nontrivial by the earlier source
noncentrality conclusion. Since the Omega actor is S₃×S₃, the residual
of its normal closure has order three or nine. The preceding transport
identifies this with the image of the literal Y. In the order-nine branch
it is the full ambient two-residual, and source 15.2.3(3) gives uniqueness
of the maximal two-local overgroup of YT.

The central extensions above these images in 15.2.3(1), and the separate
order-three choice in 15.2.6, remain separate conclusions. The noncentrality
premise is precisely the earlier 14.1.17(1) input, on the chosen V.

Source: Aschbacher--Smith, 15.2.3(1),(3), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

omit [Finite G] in
private theorem intersection_core_image_ne_bot
    {M Mc V : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (actionHom M V hn).rangeRestrict ≠ ⊥ := by
  intro he
  have hk := (Subgroup.map_eq_bot_iff _).mp he
  apply hRc
  intro x hx
  let m : M := ⟨x, ((pCoreIn_le 2 _).trans inf_le_left) hx⟩
  have hh : (actionHom M V hn) m = 1 :=
    congrArg Subtype.val (hk (show m ∈ ((M ⊓ Mc).pCoreIn 2).subgroupOf M from hx))
  have hc : m ∈ (actionHom M V hn).ker := hh
  rwa [actionHom_ker] at hc

/-- The image of the literal Y has order three or nine in the Omega row. -/
theorem source_omega_caseIIResidual_image_order (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 3 ∨
    Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9 := by
  rw [source_omega_caseIIResidual_image T hTM hn ho _
    (actionHom M V hn).rangeRestrict_surjective, residual_notation]
  exact SymmetricThreeProductResidual.normalClosure_residual_card ho.2.2.2.1.some _
    (intersection_core_image_ne_bot hn hRc)

/-- Original 14.1.17(2) in the Omega application: the literal residual image
is the commutator of the ambient odd residual with the actual core image. -/
theorem source_omega_caseIIResidual_image_commutator (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ⁅pResidual 2 (actionHom M V hn).range,
        (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (actionHom M V hn).rangeRestrict⁆ := by
  let f := (actionHom M V hn).rangeRestrict
  let P := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  rw [source_omega_caseIIResidual_image T hTM hn ho f
    (actionHom M V hn).rangeRestrict_surjective, residual_notation]
  apply SymmetricThreeProductResidual.normalClosure_residual_eq_commutator ho.2.2.2.1.some P
  exact map_mono (comap_mono hRT)

/-- The order-nine branch discharges the full-image premise in source 15.2.3(3). -/
theorem source_omega_lemma_15_2_3_3_of_image_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9) :
    maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M} := by
  apply source_omega_lemma_15_2_3_3_of_residual_image hG T hempty hM hJ hV ho
  have he := source_omega_caseIIResidual_image T (Mc := Mc) hM.1.2 hV.normalized ho
    (actionHom M V hV.normalized).rangeRestrict
    (actionHom M V hV.normalized).rangeRestrict_surjective
  rw [he, residual_notation] at hcard ⊢
  exact SymmetricThreeProductResidual.normalClosure_residual_eq_of_card_nine
    ho.2.2.2.1.some _ hcard

/-- The original Omega residual yields a proper cubic image or the full-image
uniqueness branch; no arbitrary subgroup is substituted for source Y. -/
theorem source_omega_residual_branches
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict) = 3 ∨
      (Nat.card ((Y.subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict) = 9 ∧
        maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M}) := by
  rcases source_omega_caseIIResidual_image_order T hM.1.2 hV.normalized ho hRc with h3 | h9
  · exact Or.inl h3
  · exact Or.inr ⟨h9, source_omega_lemma_15_2_3_3_of_image_nine hG T hempty hM hJ hV ho h9⟩

end CFSG.Quasithin.Chapter15.Section02
