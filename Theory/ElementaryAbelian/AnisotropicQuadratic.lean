module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.QuadraticForm.BinaryAnisotropic

/-!
# Anisotropic quadratic maps between elementary binary groups

Convert multiplicative quadratic data to the vector spaces on the additive
type tags. Over the binary field the scalar laws follow from the two possible
scalars. The anisotropic dimension bound then bounds the source order by
the square of the target order, in particular by sixteen when the target
has order four.

This is the square-map counting input for the order calculation associated
with Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.393. Its dimension
bound is a consequence of Chevalley–Warning.
-/

open Module

open scoped IsMulCommutative

namespace IsElementaryAbelian

/-- The order of the source of an anisotropic binary quadratic map is at
most the square of the target order. The laws are expressed multiplicatively
so that they apply directly to square and commutator maps. -/
public theorem card_le_sq_of_anisotropic_quadratic
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z)
    (hanisotropic : ∀ x, square x = 1 → x = 1) : Nat.card V ≤ (Nat.card W) ^ 2 := by
  let q (x : Additive V) : Additive W := Additive.ofMul (square x.toMul)
  have hq0 : q 0 = 0 := hone
  have hp (x y : Additive V) :
      QuadraticMap.polar q x y = Additive.ofMul (polar x.toMul y.toMul) := by
    change Additive.ofMul (square (x.toMul * y.toMul)) -
      Additive.ofMul (square x.toMul) - Additive.ofMul (square y.toMul) = _
    rw [hquadratic]
    simp only [ofMul_mul]
    abel
  have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  let Q : QuadraticMap (ZMod 2) (Additive V) (Additive W) :=
    QuadraticMap.ofPolar q
      (by intro a x; rcases binary a with rfl | rfl <;> simp [hq0])
      (by
        intro x y z
        simp only [hp, toMul_add, hbilinear, ofMul_mul])
      (by intro a x y; rcases binary a with rfl | rfl <;> simp [QuadraticMap.polar, hq0])
  have hQ : Q.Anisotropic := by
    intro x hx
    exact hanisotropic x.toMul hx
  have hdim := Q.finrank_le_twice_of_anisotropic_binary hQ
  have hVcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hWcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  change Nat.card V = _ at hVcard
  change Nat.card W = _ at hWcard
  simp only [Nat.card_zmod] at hVcard hWcard
  calc
    Nat.card V = 2 ^ finrank (ZMod 2) (Additive V) := hVcard
    _ ≤ 2 ^ (2 * finrank (ZMod 2) (Additive W)) :=
      Nat.pow_le_pow_right (by decide) hdim
    _ = (2 ^ finrank (ZMod 2) (Additive W)) ^ 2 := by rw [Nat.mul_comm 2, pow_mul]
    _ = (Nat.card W) ^ 2 := by rw [← hWcard]

/-- An anisotropic quadratic map to an elementary group of order four has
source order at most sixteen. -/
public theorem card_le_sixteen_of_anisotropic_quadratic
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (square : V → W) (polar : V → V → W)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z)
    (hanisotropic : ∀ x, square x = 1 → x = 1) : Nat.card V ≤ 16 := by
  have h := card_le_sq_of_anisotropic_quadratic square polar hone hquadratic hbilinear hanisotropic
  norm_num only [hW, Nat.reducePow] at h
  exact h

end IsElementaryAbelian
