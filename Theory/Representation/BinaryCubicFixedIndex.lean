module
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Theory.Representation.BinaryGroupAction

/-!
# Cubic fixed indices of doubled binary modules

A three-group acting on a binary group of order eight has fixed index at
most four: the index is a power of four and divides eight. Fixed indices
multiply on direct sums, so two such modules have fixed index at most sixteen.
This retains the same actor on both summands.

Source application: Aschbacher--Smith 13.3.12, printed p.890.
-/

public section
open Subgroup
namespace Representation.BinaryFixedPoints
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

theorem fixedIndex_le_four_of_card_eight (ρ : Representation (ZMod 2) A W)
    (hA : IsPGroup 3 A) (hW : Nat.card W = 8) : fixedIndex ρ ≤ 4 := by
  let := action ρ
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  have hi := FixedPoints.index_eq_four_pow_cubicLength
    (V := Multiplicative W) hA (IsElementaryAbelian.isPGroup 2 _)
  have hc := fixedIndex_mul_card ρ
  have hp := Nat.card_pos (α := ρ.invariants)
  have hb : fixedIndex ρ ≤ 8 := by
    rw [hW] at hc
    nlinarith
  change fixedIndex ρ = _ at hi
  rw [hi] at hb ⊢
  by_cases hk : FixedPoints.cubicLength A (Multiplicative W) ≤ 1
  · exact (Nat.pow_le_pow_right (by decide) hk).trans (by decide)
  · have hh : 4^2 ≤ 4^FixedPoints.cubicLength A (Multiplicative W) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh
    omega

variable {W' : Type*} [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W']

theorem fixedIndex_prod (ρ : Representation (ZMod 2) A W)
    (σ : Representation (ZMod 2) A W') :
    fixedIndex (ρ.prod σ) = fixedIndex ρ * fixedIndex σ := by
  let e : (ρ.prod σ).invariants ≃ ρ.invariants × σ.invariants := {
    toFun v := (⟨v.val.1,fun a => congrArg Prod.fst (v.property a)⟩,
      ⟨v.val.2,fun a => congrArg Prod.snd (v.property a)⟩)
    invFun v := ⟨(v.1.val,v.2.val),fun a => Prod.ext (v.1.property a) (v.2.property a)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have he : Nat.card (ρ.prod σ).invariants = Nat.card ρ.invariants * Nat.card σ.invariants :=
    (Nat.card_congr e).trans (Nat.card_prod _ _)
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (ρ.prod σ).invariants))
  rw [fixedIndex_mul_card,he,Nat.card_prod]
  calc
    Nat.card W * Nat.card W' = (fixedIndex ρ * Nat.card ρ.invariants) *
        (fixedIndex σ * Nat.card σ.invariants) := by rw [fixedIndex_mul_card,fixedIndex_mul_card]
    _ = _ := by ring

end Representation.BinaryFixedPoints
