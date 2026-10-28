module
public import Theory.NumberTheory.BinaryPrimitiveDivisor
import all Theory.NumberTheory.BinaryPrimitiveDivisor

/-!
# Primitive binary divisors at every positive degree divisible by four

The cyclotomic argument in the parent proves a prime of prescribed
multiplicative order for 4 at every exponent greater than one. Squaring
therefore gives a prime of binary order 4*n for every n>0; oddness of n
is unnecessary. The parent public odd-exponent interface is preserved.

This is an intentional internal proof split: `import all` accesses only
the parent's private cyclotomic existence theorem, without changing its
public boundary or copying its proof. No private name occurs in the new
public statement. The symplectic four-space binary degree bound consumes
this extension, as required by Aschbacher–Smith E.2.13(4), printed p.225.
-/

public section
namespace Theory.NumberTheory
/-- The primitive binary divisor exists for every positive exponent 4*n. -/
theorem exists_prime_orderOf_two_four_mul {n : ℕ} (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = 4 * n := by
  obtain ⟨p, hp, horder⟩ := exists_prime_orderOf_four (m := 2 * n) (by omega)
  refine ⟨p, hp, ?_⟩
  have hsquare : (2 : ZMod p) ^ 2 = 4 := by ring
  have hd : 2 ∣ orderOf (2 : ZMod p) := by
    apply dvd_trans (show 2 ∣ orderOf ((2 : ZMod p) ^ 2) by rw [hsquare, horder]; omega)
    exact orderOf_pow_dvd 2
  have he := orderOf_pow_of_dvd (by decide : 2 ≠ 0) hd
  rw [hsquare, horder] at he
  have hmul := Nat.div_mul_cancel hd
  omega
end Theory.NumberTheory
