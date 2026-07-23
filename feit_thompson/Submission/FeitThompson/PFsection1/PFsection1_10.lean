module

public import Submission.FeitThompson.Representation.CharacterValues

/-!
# Peterfalvi, Section 1, Proposition (1.10)

This file records the Lean theorem nodes for Peterfalvi (1.10).  The
cyclotomic order `ℤ[η]` and congruence modulo `1 - ξ` are supplied by
`PFtest/Representation/Cyclotomic.lean`.

Part (a) is now stated for the unbundled `Representation.IsVirtualCharacter`
predicate: a virtual character is a finite integer linear combination of
ordinary finite-dimensional representation characters, with representation
spaces encoded as `Fin n → ℂ`.  No `Rep`/`FDRep` or category-theoretic
representation API is used.

Part (b) is stated as the cyclotomic-order divisibility descent used in the
book: congruence of a rational integer modulo `1 - ξ` in `ℤ[η]` implies
ordinary divisibility by the rational prime `p`.
-/

noncomputable section

namespace Section1
universe u
universe v

open Representation

/-- Peterfalvi (1.10)(a), virtual-character form. -/
public theorem proposition_1_10_a
    {G : Type*} [Group G] [Finite G] {p : ℕ} {η ξ : ℂ}
    (hp : Nat.Prime p) (hξ : IsPrimitiveRoot ξ p)
    (hη : IsPrimitiveRoot η (Nat.card G))
    {x y : G} (hx_order : orderOf x = p) (hcomm : x * y = y * x)
    {χ : G → ℂ} (hχ : IsVirtualCharacter χ) :
    ∃ hxy : χ (x * y) ∈ cyclotomicOrder η,
      ∃ hy : χ y ∈ cyclotomicOrder η,
        CongruentModOneSub η ξ (χ (x * y)) (χ y)
          (primitive_root_mem_cyclotomicOrder_of_dvd hη
            (Nat.card_pos (α := G)).ne' hξ (by
              rw [← hx_order]
              exact orderOf_dvd_natCard x))
          hxy hy := by
  exact virtualCharacter_congruent_at_mul
    (η := η) (ξ := ξ) hξ hp.ne_zero hη
    (primitive_root_mem_cyclotomicOrder_of_dvd hη
      (Nat.card_pos (α := G)).ne' hξ (by
        rw [← hx_order]
        exact orderOf_dvd_natCard x))
    hχ hx_order hcomm

/--
Peterfalvi (1.10)(a), decomposition form retained as a lower-level helper:
integer linear combinations of linear constituents satisfy the same congruence.
-/
public theorem proposition_1_10_a_decomposition
    {G ι : Type*} [Fintype ι] [Mul G]
    {η ξ : ℂ} {x y : G} {χ : G → ℂ} {m : ι → ℤ} {α : ι → G → ℂ}
    (hχ : IsCyclotomicVirtualCharacterAt η ξ x y χ m α) :
    CongruentModOneSub η ξ (χ (x * y)) (χ y) hχ.xi_mem
      hχ.value_xy_mem hχ.value_y_mem :=
  virtual_character_congruent_at_mul hχ

/--
Peterfalvi (1.10)(b), cyclotomic-order divisibility descent.

If `ξ` is a primitive `p`-th root, `η` is integral over `ℤ`, and `ξ ∈ ℤ[η]`,
then any rational integer congruent to `0` modulo `1 - ξ` in `ℤ[η]` is
divisible by `p` in `ℤ`.
-/
public theorem proposition_1_10_b
    {p : ℕ} {η ξ : ℂ} (hp : Nat.Prime p) (hξ : IsPrimitiveRoot ξ p)
    (hη : IsIntegral ℤ η) (hξη : ξ ∈ cyclotomicOrder η) (n : ℤ)
    (hcong : CongruentModOneSub η ξ (n : ℂ) 0 hξη
      (intCast_mem_cyclotomicOrder η n)
      ((cyclotomicOrder η).zero_mem)) :
    (p : ℤ) ∣ n :=
  prime_dvd_int_of_congruent_zero_mod_one_sub hp hξ hη hξη n hcong

/--
Isaacs rational-integral descent core used internally in the proof of
Peterfalvi (1.10)(b).
-/
public theorem proposition_1_10_b_integral_quotient_core
    {p : ℕ} (hp : Nat.Prime p) (n : ℤ)
    (hquot : IsIntegral ℤ (((n ^ (p - 1) : ℤ) : ℂ) / (p : ℂ))) :
    (p : ℤ) ∣ n :=
  prime_dvd_int_of_integral_power_quotient hp n hquot

/-- The cyclotomic product identity used in the proof of (1.10)(b). -/
public theorem proposition_1_10_b_product_formula
    {p : ℕ} {ξ : ℂ} (hp : Nat.Prime p) (hξ : IsPrimitiveRoot ξ p) :
    (∏ k ∈ Finset.range (p - 1), (1 - ξ ^ (k + 1))) = (p : ℂ) :=
  primitive_root_prod_one_sub_pow_eq_prime hp hξ

end Section1
