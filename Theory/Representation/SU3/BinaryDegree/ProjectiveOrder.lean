module

public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Primitive binary primes in the order of PSU₃

The projective order formula for the antidiagonal Hermitian form transports
to every nondegenerate ternary Hermitian form over the same quadratic field.
For `q = 2^n`, a prime with binary multiplicative order `6*n` divides `q³+1`:
the element `2^(3*n)` has square one but is not one. The prime is not three,
so the projective denominator `gcd(3,q+1)` does not remove it.

This supplies the order-theoretic part of an alternative proof of the SU₃
binary minimum used in Aschbacher--Smith, printed p.356. The primitive-prime
existence input is separate. Sources: Huppert II.10.12 for the group order;
GLS3 §6.5 (the `U₃(r^b)` primitive-divisor argument) and GLS2, Chapter A,
Theorem 1.1 for the number-theoretic strategy.
-/

public section

open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

namespace Representation.SU3.BinaryDegree

/-- The actual projective group order, with no restriction on the Gram matrix. -/
theorem card_projective {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hcard hfixed
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J)
      q hcard hfixed rfl
  exact hc

/-- A positive binary multiplicative order excludes the defining prime. -/
theorem prime_ne_two_of_order {p n : ℕ} (hn : 0 < n)
    (ho : orderOf (2 : ZMod p) = 6 * n) : p ≠ 2 := by
  rintro rfl
  have hz : orderOf (2 : ZMod 2) = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero]
  omega

/-- The primitive binary prime cannot be cancelled by the scalar denominator. -/
theorem prime_ne_three_of_order {p n : ℕ}
    (ho : orderOf (2 : ZMod p) = 6 * n) : p ≠ 3 := by
  rintro rfl
  have hz := Representation.BinaryPrimeDegree.orderOf_two_mod_three
  omega

/-- A binary primitive prime at exponent `6*n` divides the unitary cubic factor. -/
theorem prime_dvd_cube_add_one {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (ho : orderOf (2 : ZMod p) = 6 * n) : p ∣ (2 ^ n) ^ 3 + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : ((2 : ZMod p) ^ (3 * n)) ^ 2 = 1 := by
    rw [← pow_mul, show 3 * n * 2 = 6 * n by omega, ← ho]
    exact pow_orderOf_eq_one _
  have hne : (2 : ZMod p) ^ (3 * n) ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ho] at hd
    have := Nat.le_of_dvd (by omega : 0 < 3 * n) hd
    omega
  have hneg : (2 : ZMod p) ^ (3 * n) = -1 :=
    (sq_eq_one_iff.mp hs).resolve_left hne
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [← pow_mul, show n * 3 = 3 * n by omega, hneg]
  ring

/-- Primitive binary primes survive in the actual projective unitary group. -/
theorem prime_dvd_card_projective {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n p : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hp : p.Prime) (ho : orderOf (2 : ZMod p) = 6 * n) :
    p ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  rw [card_projective J hcard hf]
  let q := 2 ^ n
  have hgcd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) _
  have hd : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hcop : p.Coprime (Nat.gcd 3 (q + 1)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hp3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (q + 1))
    have he := (Nat.dvd_prime Nat.prime_three).mp hp3
    exact prime_ne_three_of_order ho (he.resolve_left hp.ne_one)
  apply (hcop.dvd_mul_right).mp
  rw [Nat.div_mul_cancel hd]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (prime_dvd_cube_add_one hp hn ho) _) _

end Representation.SU3.BinaryDegree
