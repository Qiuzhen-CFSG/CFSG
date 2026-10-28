module
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# Ordered involution pairs in GL₂(3)

Exactly twenty-four ordered pairs of involutions have product whose square
is the scalar involution. Both factors in each such pair are noncentral. Every other involution
product has order dividing six.
The count is checked on pairs of two-by-two matrices over ZMod 3, then
transported to the actual general linear group by an explicit equivalence.

Source: the local count in Alperin–Brauer–Gorenstein, III.7 equation (8),
article pp.103–104, specialized to characteristic three.
-/

namespace Matrix.GeneralLinearGroup


open Matrix Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev G := GL (Fin 2) (ZMod 3)

private theorem matrix_count : (Finset.univ.filter (fun p : M × M =>
    p.1.det ≠ 0 ∧ p.2.det ≠ 0 ∧
    p.1 ≠ 1 ∧ p.1 ^ 2 = 1 ∧ p.2 ≠ 1 ∧ p.2 ^ 2 = 1 ∧
    (p.1 * p.2)^2 = threeCentral.val)).card = 24 := by
  decide +kernel

private theorem involution_iff (a : G) :
    orderOf a = 2 ↔ a.val ≠ 1 ∧ a.val ^ 2 = 1 := by
  constructor
  · intro h
    constructor
    · intro he
      have hh : a = 1 := Units.ext he
      simp [hh] at h
    · exact congrArg Units.val (h ▸ pow_orderOf_eq_one a)
  · rintro ⟨hn, hs⟩
    apply orderOf_eq_prime (p := 2) (Units.ext hs)
    intro he
    exact hn (congrArg Units.val he)

private def pairEquiv :
    {p : {a : G // orderOf a = 2} × {a : G // orderOf a = 2} //
      ((p.1 : G) * p.2)^2 = threeCentral} ≃
    {p : M × M // p.1.det ≠ 0 ∧ p.2.det ≠ 0 ∧
      p.1 ≠ 1 ∧ p.1 ^ 2 = 1 ∧ p.2 ≠ 1 ∧ p.2 ^ 2 = 1 ∧
      (p.1 * p.2)^2 = threeCentral.val} where
  toFun p := ⟨(p.val.1.val.val, p.val.2.val.val),
    Units.ne_zero (det p.val.1.val), Units.ne_zero (det p.val.2.val),
    (involution_iff _).mp p.val.1.property |>.1,
    (involution_iff _).mp p.val.1.property |>.2,
    (involution_iff _).mp p.val.2.property |>.1,
    (involution_iff _).mp p.val.2.property |>.2,
    congrArg Units.val p.property⟩
  invFun p := ⟨(⟨mkOfDetNeZero p.val.1 p.property.1,
      (involution_iff _).mpr ⟨p.property.2.2.1, p.property.2.2.2.1⟩⟩,
    ⟨mkOfDetNeZero p.val.2 p.property.2.1,
      (involution_iff _).mpr ⟨p.property.2.2.2.2.1, p.property.2.2.2.2.2.1⟩⟩),
      Units.ext p.property.2.2.2.2.2.2⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext (Units.ext rfl))
    (Subtype.ext (Units.ext rfl)))
  right_inv _ := rfl

/-- There are twenty-four ordered involution pairs whose product squares to −I. -/
public theorem three_involution_pair_square_central_card : Nat.card
    {p : {a : GL (Fin 2) (ZMod 3) // orderOf a = 2} ×
      {a : GL (Fin 2) (ZMod 3) // orderOf a = 2} //
      ((p.1 : GL (Fin 2) (ZMod 3)) * p.2)^2 = threeCentral} = 24 := by
  rw [Nat.card_congr pairEquiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact matrix_count

private theorem matrix_central_factor : ∀ a b : M,
    a ^ 2 = 1 → b ^ 2 = 1 → (a * b) ^ 2 = threeCentral.val →
      a ≠ threeCentral.val ∧ b ≠ threeCentral.val := by
  decide +kernel

/-- Both factors of a pair counted by the order-four section are noncentral. -/
public theorem three_involution_pair_square_central_noncentral
    (a b : GL (Fin 2) (ZMod 3)) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : (a * b) ^ 2 = threeCentral) : a ≠ threeCentral ∧ b ≠ threeCentral := by
  have h := matrix_central_factor a.val b.val
    ((involution_iff a).mp ha).2 ((involution_iff b).mp hb).2
    (congrArg Units.val hab)
  exact ⟨fun he => h.1 (congrArg Units.val he), fun he => h.2 (congrArg Units.val he)⟩

private theorem matrix_product_six_or_square_central : ∀ a b : M,
    a ^ 2 = 1 → b ^ 2 = 1 →
      (a * b) ^ 6 = 1 ∨ (a * b) ^ 2 = threeCentral.val := by
  decide +kernel

/-- A product of involutions has order dividing six or squares to −I.
In particular no order-eight section occurs among these products. -/
public theorem three_involution_product_six_or_square_central
    (a b : GL (Fin 2) (ZMod 3)) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    (a * b) ^ 6 = 1 ∨ (a * b) ^ 2 = threeCentral := by
  rcases matrix_product_six_or_square_central a.val b.val
      ((involution_iff a).mp ha).2 ((involution_iff b).mp hb).2 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

end Matrix.GeneralLinearGroup
