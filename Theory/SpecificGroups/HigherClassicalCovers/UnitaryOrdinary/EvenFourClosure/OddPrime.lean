module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.Cyclotomic
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.NormOne
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.SplitTorus

/-!+# Odd-prime support of binary SU₄ covering kernels

For q = 2^n, cyclic-Sylow transfer excludes primes outside q²−1, and
the rank-three norm-one torus calculation excludes every odd prime
dividing q+1, including the nonabelian three-primary cases. Thus an
odd prime in a perfect central kernel must divide q−1. The explicit
paired-torus calculation excludes those remaining primes once its
ambient primary-order bound is supplied.

The last bound remains an explicit hypothesis of the assembly below.
These results do not yet supply the unconditional `hodd` argument to
`EvenFourClosure.injective_of_prime_kernel_exclusions`. The prime-kernel
quotient application is included, so final assembly needs only discharge
the stated numerical bound; no double-cover input is used.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`, and GLS3 §6.1. The canonical multiplier has order
gcd(4,q+1)=1, and there are no odd exceptional multipliers in this range.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime

universe u
variable {F : Type u} [Field F] [Finite F]

/-- Every odd prime remaining in the literal covering kernel divides q−1. -/
theorem kernel_prime_dvd_predecessor
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J))
    (hd : p ∣ Nat.card d.toMonoidHom.ker) : p ∣ 2 ^ n - 1 := by
  have hs : p ∣ (2 ^ n) ^ 2 - 1 := by
    by_contra h
    exact not_dvd_kernel_of_not_dvd_sq_sub_one J n hn hcard hconj hp h d hd
  have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa only [one_pow] using Nat.sq_sub_sq (2 ^ n) 1
  rw [he] at hs
  rcases (Fact.out : p.Prime).dvd_mul.mp hs with hplus | hminus
  · exact (not_dvd_kernel_of_dvd_succ J n hn hcard hconj hp hplus d hd).elim
  · exact hminus

/-- The sole remaining split-primary order bound completes the exact
prime-kernel exclusion needed by `EvenFourClosure`'s `hodd` input. -/
theorem prime_kernel_ne_of_split_bounds
    (J : HermitianForm 4 F) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hsplit : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
      ¬ p * primaryExponent (2 ^ n) p ^ 2 ∣ Nat.card (Standard J))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (d : Cover E (Standard J)) :
    Nat.card d.toMonoidHom.ker ≠ p := by
  let : Fact p.Prime := ⟨hp⟩
  intro he
  have hd : p ∣ Nat.card d.toMonoidHom.ker := he ▸ dvd_rfl
  have hm := kernel_prime_dvd_predecessor J n (by omega) hcard hconj hp2 d hd
  exact not_dvd_kernel_of_split_card_bound J n (by omega) hcard hconj hp2
    (hsplit p hp hp2 hm) d hd

/-- The prime-kernel quotient reduction excludes each odd prime from an
arbitrary covering kernel once the remaining split-primary bound is proved. -/
theorem not_dvd_card_kernel_of_split_bounds
    (J : HermitianForm 4 F) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hsplit : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
      ¬ p * primaryExponent (2 ^ n) p ^ 2 ∣ Nat.card (Standard J))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Type u} [Group E] [Finite E] (d : Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  apply d.not_dvd_card_kernel_of_no_prime_kernel
  intro D _ _ c
  exact prime_kernel_ne_of_split_bounds J n hn hcard hconj hsplit p hp hp2 c

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
