module

public import Theory.NumberTheory.BinaryPrimitiveDivisor.SixMultiple
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.SpecificGroups.Triality.Model.QTKE
import Mathlib.Tactic.Ring

/-!
# A primitive-prime degree bound for binary triality

Every faithful finite-dimensional binary representation of the genuine
`Standard.BinaryCarrier n hn` has dimension at least `12*n`, for every `n > 0`.
Irreducibility is not required. The carrier is the elementary graph-field fixed
subgroup modulo its own center, as in `StandardModel`.

A primitive prime at exponent `12*n` divides the factor `q^8 + q^4 + 1` of
the carrier order, where `q = 2^n`. Over the prime field, the identity
`(q^4 - 1) * (q^8 + q^4 + 1) = q^12 - 1` proves divisibility, since the
exact order excludes `q^4 = 1`. The faithful binary general-linear-group
degree bound then gives the result.

Sources: primitive primes in GLS2, Chapter A, Theorem 1.1
(`refs/KGroup/GLS2/ChapterA.tex`); the genuine fixed-cell order calculation
from GLS3 §§2.3–2.4 (`refs/KGroup/GLS3/chapter2.tex`). This gives an alternative
degree estimate for the triality exclusion on Aschbacher–Smith printed p.356
(PDF p.367, `refs/quasithin.pdf`) when `n ≥ 2`. At `n = 1` it gives only
dimension at least twelve, not the stronger `24*n` minimum used in the source.
-/

public section

namespace Triality.PrimitiveDegree

open Triality.Standard

private theorem prime_dvd_factor {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (ho : orderOf (2 : ZMod p) = 12 * n) :
    p ∣ (2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpow : ((2 : ZMod p) ^ n) ^ 12 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 12, ← ho]
    exact pow_orderOf_eq_one _
  have hfour : ((2 : ZMod p) ^ n) ^ 4 ≠ 1 := by
    intro hh
    rw [← pow_mul] at hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ho] at hd
    have hle := Nat.le_of_dvd (by omega : 0 < n * 4) hd
    omega
  have hz : (((2 : ZMod p) ^ n) ^ 4 - 1) *
      (((2 : ZMod p) ^ n) ^ 8 + ((2 : ZMod p) ^ n) ^ 4 + 1) = 0 := by
    calc
      _ = ((2 : ZMod p) ^ n) ^ 12 - 1 := by ring
      _ = 0 := by rw [hpow, sub_self]
  have hfactor := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hfour)
  exact (ZMod.natCast_eq_zero_iff _ p).mp (by simpa using hfactor)

/-- The actual triality carrier has an odd prime divisor of binary order `12*n`.
Its divisibility follows from the proved fixed Bruhat cell count. -/
theorem exists_prime_dvd_card (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (BinaryCarrier n hn) ∧
      orderOf (2 : ZMod p) = 12 * n := by
  obtain ⟨p, hp, ho⟩ :=
    Theory.NumberTheory.exists_prime_orderOf_two_six_mul (n := 2 * n) (by omega)
  have ho' : orderOf (2 : ZMod p) = 12 * n := by omega
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    change orderOf (0 : ZMod 2) = 12 * n at ho'
    rw [orderOf_zero] at ho'
    omega
  refine ⟨p, hp, hp2, ?_, ho'⟩
  change p ∣ Nat.card (Carrier (binaryParameters n hn))
  rw [ConcreteBruhat.FixedCellCount.card_carrier n hn, binaryParameters_q]
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_right (prime_dvd_factor hn hp ho') _) _

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful binary triality representation has dimension at least `12*n`,
including at `n = 1`, without an irreducibility assumption. -/
theorem finrank_ge (n : ℕ) (hn : 0 < n)
    (ρ : Representation (ZMod 2) (BinaryCarrier n hn) V)
    (hρ : Function.Injective ρ) : 12 * n ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨p, hp, hp2, hdiv, ho⟩ := exists_prime_dvd_card n hn
  rw [← ho]
  exact Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ hp hp2 hdiv

end Triality.PrimitiveDegree
