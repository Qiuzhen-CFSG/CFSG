module
public import Theory.SpecificGroups.PSL2.SixteenWreathComponents

/-!
# The quintic part of the exchanged PSL₂(16) wreath model

The simple centerless inner subgroup and the field outer quotient compute
only the order needed for Sylow-five transport. In particular the actual
wreath model has no factor 125 in its order. The Chapter14 consumer uses
this to show that the original H contains a full Sylow-five subgroup of Mc.
Source: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1034.
-/
public section
open Subgroup
namespace Theory.PSL2.SixteenWreathComponents

theorem model_card : Nat.card L = 4080 := by
  rw [←Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    GaloisField.card 2 4 (by decide)]
  decide

theorem wreath_card : Nat.card W = 532684800 := by
  have hz : center L = ⊥ := by
    let := simple
    let := perfect
    exact (inferInstance : (center L).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp he))
  have hi : Nat.card (MulAut.innerSubgroup L) = 4080 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot hz)).toEquiv]
    exact model_card
  have ho : (MulAut.innerSubgroup L).index = 4 :=
    Theory.PSL2.outer_card_eq_field_degree (GaloisField 2 4)
      (GaloisField.card 2 4 (by decide))
  have ha : Nat.card (MulAut L) = 16320 := by
    rw [←(MulAut.innerSubgroup L).card_mul_index,hi,ho]
  rw [RegularWreathProduct.card,ha]
  norm_num [Nat.card_eq_fintype_card]

/-- The wreath model has exactly two factors of five in its order. -/
theorem not_five_cube_dvd_card : ¬125 ∣ Nat.card W := by
  rw [wreath_card]
  decide

end Theory.PSL2.SixteenWreathComponents
