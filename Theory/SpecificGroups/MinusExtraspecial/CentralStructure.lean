module

public import Theory.SpecificGroups.MinusExtraspecial.Model
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The center of the quaternion–dihedral central product

The center of the concrete `Q₈ * D₈` is its common involution line. Every
square is central, and the central quotient has order sixteen and exponent
two. These facts verify the extraspecial structure of the concrete model.

The finite calculations use its quaternion and binary coordinates. Source:
the central product in Aschbacher–Smith, *The Classification of Quasithin
Groups*, I.4.7, printed p. 418; the factor embeddings are in `Model`.
-/

namespace MinusExtraspecial

public theorem mem_center_iff (x : Model) :
    x ∈ Subgroup.center Model ↔ x = 1 ∨ x = quaternion z := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide +kernel

public theorem card_center : Nat.card (Subgroup.center Model) = 2 := by
  calc
    _ = Nat.card {x : Model // x = 1 ∨ x = quaternion z} :=
      Nat.card_congr (Equiv.subtypeEquivRight mem_center_iff)
    _ = 2 := by rw [Nat.card_eq_fintype_card]; decide +kernel

public theorem square_mem_center (x : Model) : x ^ 2 ∈ Subgroup.center Model := by
  rw [mem_center_iff]
  revert x
  decide +kernel

public theorem card_central_quotient :
    Nat.card (Model ⧸ Subgroup.center Model) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Model)
  rw [card_model, card_center] at h
  omega

public instance model_isExtraspecial : IsExtraspecial 2 Model where
  center_order_p := card_center
  quotient_elementary_abelian := by
    have hp (x : Model ⧸ Subgroup.center Model) : x ^ 2 = 1 := by
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact square_mem_center x
    have hi (x : Model ⧸ Subgroup.center Model) : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp x)
    exact {
      toIsMulCommutative := isMulCommutative_iff.mpr fun a b => by
        calc
          a * b = (a * b)⁻¹ := (hi _).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
          _ = b * a := by rw [hi, hi]
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
  quotient_nontrivial := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [card_central_quotient]; decide)

end MinusExtraspecial
