module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.LinearCombination

/-!
# Prime-order roots under coefficient reduction

A primitive root of prime order stays primitive under a ring map between
domains when that prime is nonzero in the target. Its geometric sum excludes
collapse to one. For a primitive fifth root, the two real periods have
squared difference five, so they remain distinct away from characteristic five.

These elementary cyclotomic identities are used to distinguish reduced
ordinary characters; the coefficient map need not be injective.
-/

public section

namespace IsPrimitiveRoot

/-- Reduction preserves a primitive root of prime order different from the
residue characteristic, even when the coefficient map has a kernel. -/
theorem map_of_prime_ne_zero {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    {p : ℕ} (hp : p.Prime) {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (f : R →+* S) (hpS : (p : S) ≠ 0) : IsPrimitiveRoot (f ζ) p := by
  classical
  apply isPrimitiveRoot_of_mem_nthRootsFinset hp
  · exact (Polynomial.mem_nthRootsFinset hp.pos 1).mpr
      (by simpa using congrArg f hζ.pow_eq_one)
  · intro h
    have hs := congrArg f (hζ.geom_sum_eq_zero hp.one_lt)
    simp only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at hs
    exact hpS hs

/-- The discriminant identity for the two fifth-root periods. -/
theorem fifth_period_difference_sq {K : Type*} [CommRing K] [IsDomain K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ((ζ + ζ ^ 4) - (ζ ^ 2 + ζ ^ 3)) ^ 2 = 5 := by
  have hs := hζ.geom_sum_eq_zero (by decide : 1 < 5)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero] at hs
  linear_combination (ζ ^ 4 - 3 * ζ ^ 3 + ζ ^ 2 + 5 * ζ - 5) * hs

/-- The fifth-root periods separate characters in every characteristic
different from five. -/
theorem fifth_periods_ne {K : Type*} [CommRing K] [IsDomain K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hfive : (5 : K) ≠ 0) :
    ζ + ζ ^ 4 ≠ ζ ^ 2 + ζ ^ 3 := by
  intro heq
  have hs := hζ.fifth_period_difference_sq
  rw [heq, sub_self, zero_pow (by decide : 2 ≠ 0)] at hs
  exact hfive hs.symm

end IsPrimitiveRoot
