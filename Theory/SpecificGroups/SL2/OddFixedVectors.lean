module
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd-order fixed vectors in the natural SL₂ module

A matrix fixing a nonzero vector in characteristic two has square one.
If it also has an odd annihilating exponent, coprimality forces it to be
the identity. This applies to all odd tori, regardless of the field order.
Source application: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
namespace Matrix.SL2
open scoped MatrixGroups
variable {F : Type*} [Field F] [CharP F 2]

/-- A nonidentity matrix of odd order has no nonzero natural fixed vector. -/
theorem odd_power_fixed_eq_zero (a : SL(2,F))
    (m : ℕ) (hm : Odd m) (ha : a ^ m = 1) (hne : a ≠ 1)
    (v : Fin 2 → F) (hfix : a.val *ᵥ v = v) : v = 0 := by
  by_contra hv
  apply hne
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [←hm.coprime_two_left.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one
    (pow_two_eq_one_of_nonzero_fixed a v hv hfix)) (orderOf_dvd_of_pow_eq_one ha)

end Matrix.SL2
