module

public import Mathlib.GroupTheory.Index

/-!
# Cardinality of an arbitrary subgroup set product

For subgroups X and Y of a finite group, the actual set product satisfies
`|XY| |X ∩ Y| = |X| |Y|`. Neither subgroup is assumed to normalize the
other, and XY is not assumed to be a subgroup.

Mathlib's coset product formula expresses |XY| as |Y| times the number
of cosets of Y met by X. The latter coset set is in bijection with
`X/(Y ∩ X)`, viewed as a quotient set. Lagrange's formula inside X then
gives the required cardinal identity. All quotients here are coset
spaces, so no normality hypothesis enters the proof.

This is the standard finite subgroup product formula used in the
cardinality argument for binary fixed-point factorizations, in particular
the two-group-actor case of Kurzweil–Stellmacher, *The Theory of Finite
Groups*, 11.2.1. The proof uses only Mathlib's coset and relative-index APIs.
-/

open scoped Pointwise

namespace Subgroup

/-- The cardinality formula for the set product of arbitrary finite-group
subgroups, without any normalization assumption. -/
public theorem card_set_mul_mul_card_inf
    {G : Type*} [Group G] [Finite G] (X Y : Subgroup G) :
    Nat.card ((X : Set G) * (Y : Set G)) * Nat.card (X ⊓ Y : Subgroup G) =
      Nat.card X * Nat.card Y := by
  let f : X ⧸ Y.subgroupOf X → ((X : Set G).image (QuotientGroup.mk : G → G ⧸ Y)) :=
    Quotient.lift (fun x : X => ⟨QuotientGroup.mk (x : G), ⟨x, x.property, rfl⟩⟩)
      (by
        intro x y h
        apply Subtype.ext
        apply Quotient.sound
        have hx : x⁻¹ * y ∈ Y.subgroupOf X :=
          (QuotientGroup.leftRel_apply (s := Y.subgroupOf X)).mp h
        apply (QuotientGroup.leftRel_apply (s := Y)).mpr
        exact hx)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      induction x using Quotient.inductionOn with | h x =>
        induction y using Quotient.inductionOn with | h y =>
          apply Quotient.sound
          have hv : (QuotientGroup.mk (x : G) : G ⧸ Y) = QuotientGroup.mk (y : G) :=
            congrArg Subtype.val h
          have hx : (x : G)⁻¹ * (y : G) ∈ Y :=
            (QuotientGroup.eq (s := Y)).mp hv
          apply (QuotientGroup.leftRel_apply (s := Y.subgroupOf X)).mpr
          exact hx
    · rintro ⟨z, x, hx, rfl⟩
      exact ⟨QuotientGroup.mk (⟨x, hx⟩ : X), rfl⟩
  have himage : Nat.card ((X : Set G).image (QuotientGroup.mk : G → G ⧸ Y)) =
      Y.relIndex X :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (X ⊓ Y) X bot_le inf_le_left
  simp only [relIndex_bot_left, inf_relIndex_left] at hcard
  rw [card_mul_eq_card_subgroup_mul_card_quotient, himage]
  calc
    Nat.card Y * Y.relIndex X * Nat.card (X ⊓ Y : Subgroup G) =
        (Nat.card (X ⊓ Y : Subgroup G) * Y.relIndex X) * Nat.card Y := by ac_rfl
    _ = Nat.card X * Nat.card Y := by rw [hcard]

end Subgroup
