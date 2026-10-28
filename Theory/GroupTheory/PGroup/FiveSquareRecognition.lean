module
public import Theory.Representation.BinaryPermutation.FiveInvariantQuadratic
public import Theory.SpecificGroups.MinusExtraspecial.Recognition

/-!
# Recognizing an extraspecial group from its five-point square map

The image of an elementary subgroup in the central quotient is singular,
so has order at most two; its kernel has order at most two as well.
For an extraspecial group of order 32 this identifies the concrete
quaternion–dihedral central product. The coordinates are on the literal
central quotient, and square-one representatives are retained.

Source: Aschbacher–Smith 14.2.16 and I.4.7, printed pp.985–986,418.
-/

public noncomputable section
open Subgroup Module Representation
open scoped IsMulCommutative

namespace IsExtraspecial
open BinaryPermutation
variable {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q]
    [IsElementaryAbelian 2 (Q ⧸ center Q)]

theorem elementary_card_le_four_of_five_square_coordinates
    (c : Additive (Q ⧸ center Q) ≃ₗ[ZMod 2] core (Fin 5))
    (hs : ∀ u : Q, u ^ 2 = 1 →
      FiveGeometry.form (c (Additive.ofMul (QuotientGroup.mk' (center Q) u))) = 0)
    (A : Subgroup Q) [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  let f : A →* Multiplicative (core (Fin 5)) := {
    toFun a := Multiplicative.ofAdd (c (Additive.ofMul (QuotientGroup.mk' (center Q) a.val)))
    map_one' := by simp
    map_mul' := by
      intro a b
      change c (Additive.ofMul (QuotientGroup.mk' (center Q) (a.val * b.val))) = _
      rw [map_mul]
      exact c.map_add _ _ }
  have hr : Nat.card f.range ≤ 2 := FiveGeometry.card_le_two_of_all_singular f.range (by
    rintro ⟨x,a,ha⟩
    change FiveGeometry.form x.toAdd = 0
    rw [←ha]
    exact hs a.val (congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a)))
  let j : f.ker → center Q := fun a => ⟨a.val.val,by
    apply (QuotientGroup.eq_one_iff _).mp
    have hh : c (Additive.ofMul (QuotientGroup.mk' (center Q) a.val.val)) = 0 := a.property
    exact c.injective (hh.trans (map_zero c).symm)⟩
  have hj : Function.Injective j := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : center Q => (x : Q)) hh
  have hk : Nat.card f.ker ≤ 2 := (Nat.card_le_card_of_injective j hj).trans_eq
    (IsExtraspecial.center_order_p 2 Q)
  have hc : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    rw [←index_ker]
    exact f.ker.card_mul_index
  nlinarith

theorem minus_model_of_five_square_coordinates
    (hcard : Nat.card Q = 32)
    (c : Additive (Q ⧸ center Q) ≃ₗ[ZMod 2] core (Fin 5))
    (hs : ∀ u : Q, u ^ 2 = 1 →
      FiveGeometry.form (c (Additive.ofMul (QuotientGroup.mk' (center Q) u))) = 0) :
    Nonempty (Q ≃* MinusExtraspecial.Model) := by
  apply exists_mulEquiv_minusExtraspecial_model ?_ hcard
  intro A hA
  let := hA
  have hh := elementary_card_le_four_of_five_square_coordinates c hs A
  omega
end IsExtraspecial
