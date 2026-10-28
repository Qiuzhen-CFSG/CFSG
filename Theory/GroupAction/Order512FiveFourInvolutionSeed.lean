module

public import Theory.GroupAction.Order512FiveFourSquareIdentities
public import Theory.GroupAction.FiveFourSquareSeed

/-!
# Lifting the five-four square zero to an actual involution

A nonidentity zero in the square quotient has a lift whose square is central.
Perfectness supplies a nonzero commutator row on the elementary subgroup.
Since the center has order two, multiplying the lift by a suitable element of
that subgroup kills its square. The five-four action is needed only on the
two quotient layers, and is not assumed to split on the whole group.
-/

namespace Theory.GroupAction.Order512FiveFour
open Subgroup
open scoped commutatorElement IsMulCommutative

variable {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries P 2)
    (hsq : ∀ x : P, x ^ 2 ∈ D)
    (eZ : center P ≃* Multiplicative (ZMod 2))

/-- A nonzero square-map zero lifts to an actual involution in its original coset. -/
public theorem involutory_lift_of_square_zero
    (hinj : Function.Injective (squarePairing D hD eZ))
    (v : P ⧸ D) (hv : v ≠ 1)
    (hq : elementarySecondCenterSquare D hD hsq v = 1) :
    ∃ b : P, b ^ 2 = 1 ∧ QuotientGroup.mk' D b = v := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
  have hxc : x ^ 2 ∈ center P :=
    (elementarySecondCenterSquare_eq_one_iff D hD hsq x).mp hq
  by_cases hx : x ^ 2 = 1
  · exact ⟨x, hx, rfl⟩
  have hrow : squarePairing D hD eZ (QuotientGroup.mk' D x) ≠ 1 := by
    intro hh
    exact hv (hinj (hh.trans (map_one _).symm))
  have hex : ∃ w, squarePairing D hD eZ (QuotientGroup.mk' D x) w ≠ 1 := by
    by_contra! hall
    exact hrow (MonoidHom.ext hall)
  obtain ⟨w, hw⟩ := hex
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((center P).subgroupOf D) w
  rw [squarePairing_apply] at hw
  have hc : ⁅(d : P), x⁆ ≠ 1 := by
    intro hh
    apply hw
    rw [← eZ.map_one, eZ.injective.eq_iff]
    exact Subtype.ext hh
  have hZcard : Nat.card (center P) = 2 := by
    rw [Nat.card_congr eZ.toEquiv]
    exact Nat.card_zmod 2
  obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp hZcard
  have he : ⁅(d : P), x⁆ = x ^ 2 := by
    have hcne : (⟨⁅(d : P), x⁆, bracket_mem D hD d x⟩ : center P) ≠ 1 :=
      fun hh => hc (congrArg Subtype.val hh)
    have hxne : (⟨x ^ 2, hxc⟩ : center P) ≠ 1 :=
      fun hh => hx (congrArg Subtype.val hh)
    exact congrArg Subtype.val ((huniq _ hcne).trans (huniq _ hxne).symm)
  have hd2 : (d : P) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _ d.property
  have hdi : (d : P)⁻¹ = d :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd2)
  have hx4 : x ^ 2 * x ^ 2 = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hsq x)
  refine ⟨(d : P) * x, ?_, ?_⟩
  · calc
      ((d : P) * x) ^ 2 = ⁅(d : P), x⁆ * x ^ 2 := by
        rw [commutatorElement_def, hdi]
        simp only [pow_two]
        group
      _ = 1 := by rw [he, hx4]
  · have hdq : QuotientGroup.mk' D (d : P) = 1 :=
      (QuotientGroup.eq_one_iff (N := D) (d : P)).mpr d.property
    rw [map_mul, hdq, one_mul]

/-- Faithful five-four actions on the two actual layers force an involution
outside the elementary second-center subgroup. -/
public theorem exists_involution_outside_of_five_four_layers
    [Finite P] [IsElementaryAbelian 2 (P ⧸ D)]
    (hcomm : _root_.commutator P ≤ D)
    (hV : Nat.card (P ⧸ D) = 16)
    (hW : Nat.card (D ⧸ (center P).subgroupOf D) = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (leftAction : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →*
      MulAut (P ⧸ D))
    (rightAction : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →*
      MulAut (D ⧸ (center P).subgroupOf D))
    (hl : Function.Injective leftAction) (hr : Function.Injective rightAction)
    (hequiv : ∀ a v w, squarePairing D hD eZ (leftAction a v) (rightAction a w) =
      squarePairing D hD eZ v w)
    (hqequiv : ∀ a v, elementarySecondCenterSquare D hD hsq (leftAction a v) =
      rightAction a (elementarySecondCenterSquare D hD hsq v)) :
    ∃ b : P, b ^ 2 = 1 ∧ b ∉ D := by
  let : IsElementaryAbelian 2 (D ⧸ (center P).subgroupOf D) := {
    exponent_dvd_p := (MonoidHom.exponent_dvd (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  have hinj := (squarePairing_bijective D hD eZ (hW.trans hV.symm)).1
  obtain ⟨v, hv, hq⟩ := five_four_square_has_nontrivial_zero hV hW φ hφ
    leftAction rightAction hl hr (squarePairing D hD eZ) hinj hequiv
    (elementarySecondCenterSquare D hD hsq)
    (elementarySecondCenterSquare_one D hD hsq)
    (elementarySecondCenterSquare_seven_term D hD hsq hcomm)
    (squarePairing_self D hD eZ hsq) hqequiv
    (squarePairing_commutator D hD hsq hcomm eZ)
  obtain ⟨b, hb, hqb⟩ := involutory_lift_of_square_zero D hD hsq eZ hinj v hv hq
  exact ⟨b, hb, fun h => hv (hqb.symm.trans ((QuotientGroup.eq_one_iff b).mpr h))⟩

end Theory.GroupAction.Order512FiveFour
