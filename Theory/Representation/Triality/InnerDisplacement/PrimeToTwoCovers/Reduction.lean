module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.LocalCriteria
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Reduction of triality central covers to odd Sylow geometry

The literal isomorphism R/Z(R) ≃ ³D₄(2ⁿ) gives a marked perfect central
cover whose kernel is exactly Z(R). Local Sylow geometry excludes odd
primes from this kernel by central transfer. Only prime divisors of the
base group's order need geometric witnesses.

The remaining concrete calculations separate into Sylow three, primes
greater than three dividing q²−1, and the other odd prime divisors. These
are explicit premises below, including at n = 1. No unconditional
triality multiplier theorem is asserted by this reduction.

Source: Guralnick--Malle II §8, internal p.53, and GLS3 Theorem 6.1.4
with Tables 6.1.2--3. Triality occurs in neither multiplier exception
table; in particular there is no odd-multiplier exception at q = 2.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers

open PerfectCentralCovering
open PerfectCentralCovering.OddSylow

/-- Transport the local transfer calculation through the original central
quotient. Perfectness suffices; no model simplicity theorem is required. -/
theorem center_isTwoGroup_of_sylow_geometry {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    (hlocal : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      p ∣ Nat.card (Standard.BinaryCarrier n hn) →
      Geometry p (Standard.BinaryCarrier n hn)) :
    IsPGroup 2 (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact kernel_isTwoGroup (centralQuotientCover e) hlocal

/-- Three independent families of local calculations supply every odd
prime. The exponent-one case is retained in each premise. -/
theorem center_isTwoGroup_of_prime_branches {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    (hthree : Geometry 3 (Standard.BinaryCarrier n hn))
    (hquadratic : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      p ∣ (2 ^ n) ^ 2 - 1 → Geometry p (Standard.BinaryCarrier n hn))
    (hother : ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ¬ p ∣ (2 ^ n) ^ 2 - 1 → p ∣ Nat.card (Standard.BinaryCarrier n hn) →
      Geometry p (Standard.BinaryCarrier n hn)) :
    IsPGroup 2 (Subgroup.center R) := by
  apply center_isTwoGroup_of_sylow_geometry n hn hmodel
  intro p hp hp2 hpdiv
  by_cases hp3 : p = 3
  · subst p
    exact hthree
  have hlarge : 3 < p := by have := (Fact.out : p.Prime).two_le; omega
  by_cases hquad : p ∣ (2 ^ n) ^ 2 - 1
  · exact hquadratic p hlarge hquad
  · exact hother p hlarge hquad hpdiv

end Triality.InnerDisplacement.PrimeToTwoCovers
