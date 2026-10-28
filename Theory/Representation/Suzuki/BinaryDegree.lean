module

public import Theory.NumberTheory.BinaryPrimitiveDivisor
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic

/-!
# Binary degrees of faithful Suzuki representations

Write `n = 2*k+1` and `q = 2^n`. A prime `p` for which the multiplicative
order of `2` modulo `p` is `4*n` divides `q²+1`, hence divides the order of
the concrete Suzuki matrix group. The binary general linear group order
formula then forces every faithful binary representation to have dimension
at least `4*n`. Irreducibility is not needed for this argument.

The required prime exists for every odd `n ≥ 3` by the special case of
Zsigmondy's theorem proved in `Theory.NumberTheory.BinaryPrimitiveDivisor`.
Thus `finrank_ge` gives the unconditional bound for every `k ≥ 1`, and
`finrank_ge_of_irreducible` states it in the form used by the quasithin
consumer. The explicit bound `12` for `Sz(8)` also follows directly from
the prime `13`.

The intended minimum is used in Aschbacher--Smith, *The Classification of
Quasithin Groups*, combined manuscript of 1 March 2004, printed p.356
(PDF p.367). The source obtains it from GLS3 §2.8. The prime-divisor
argument here supplies an alternative that also bounds reducible faithful
representations. The group order formula is Huppert--Blackburn III, XI.3.3;
it is reused on `BenderSuzuki.MatrixGroups.SuzukiMatrixGroup` itself.
-/

public section

namespace Representation.Suzuki

open BenderSuzuki.MatrixGroups

/-- A prime of binary multiplicative order `4*(2*k+1)` divides the order
of the actual Suzuki matrix group. -/
theorem prime_dvd_card_of_orderOf_two {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime)
    (horder : orderOf (2 : ZMod p) = 4 * (2 * k + 1)) :
    p ∣ Nat.card (SuzukiMatrixGroup k) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpow : ((2 : ZMod p) ^ (2 * k + 1)) ^ 2 = -1 := by
    have hsq : (((2 : ZMod p) ^ (2 * k + 1)) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_mul,
        show (2 * k + 1) * (2 * 2) = 4 * (2 * k + 1) by omega, ← horder]
      exact pow_orderOf_eq_one _
    apply (sq_eq_one_iff.mp hsq).resolve_left
    intro h
    rw [← pow_mul] at h
    have hle := orderOf_le_of_pow_eq_one (by omega : 0 < (2 * k + 1) * 2) h
    rw [horder] at hle
    omega
  have hdiv : p ∣ (2 ^ (2 * k + 1)) ^ 2 + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      hpow, neg_add_cancel]
  rw [suzukiMatrixGroup_card k (by omega)]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdiv _) _

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A primitive prime divisor at exponent `4*(2*k+1)` forces the full
Suzuki binary degree bound on every faithful representation. The existence
of the prime is the only extra premise. -/
theorem finrank_ge_of_primitive_prime {k p : ℕ} (hk : 1 ≤ k)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup k) V)
    (hρ : Function.Injective ρ) (hp : p.Prime)
    (horder : orderOf (2 : ZMod p) = 4 * (2 * k + 1)) :
    4 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at horder
    omega
  have hdegree := BinaryPrimeDegree.orderOf_le_finrank ρ hρ hp hp2
    (prime_dvd_card_of_orderOf_two hk hp horder)
  rwa [horder] at hdegree

/-- Every faithful binary representation of `Sz(2^(2*k+1))`, for `k ≥ 1`,
has dimension at least `4*(2*k+1)`. The space is arbitrary and the
representation need not be irreducible. -/
theorem finrank_ge {k : ℕ} (hk : 1 ≤ k)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup k) V)
    (hρ : Function.Injective ρ) :
    4 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨p, hp, horder⟩ :=
    Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
      (n := 2 * k + 1) ⟨k, rfl⟩ (by omega)
  exact finrank_ge_of_primitive_prime hk ρ hρ hp horder

/-- The universal faithful irreducible Suzuki binary degree bound used on
printed p.356 of Aschbacher--Smith, in the concrete Suzuki matrix model. -/
theorem finrank_ge_of_irreducible {k : ℕ} (hk : 1 ≤ k)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup k) V)
    (_hirr : ρ.IsIrreducible) (hρ : Function.Injective ρ) :
    4 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V :=
  finrank_ge hk ρ hρ

/-- Every faithful binary representation of `Sz(8)` has dimension at least
twelve. In particular this covers every faithful irreducible on an
arbitrary finite-dimensional binary space. -/
theorem twelve_le_finrank
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 1) V)
    (hρ : Function.Injective ρ) : 12 ≤ Module.finrank (ZMod 2) V := by
  exact finrank_ge_of_primitive_prime (by decide) ρ hρ (by decide : Nat.Prime 13)
    BinaryPrimeDegree.orderOf_two_mod_thirteen

end Representation.Suzuki
