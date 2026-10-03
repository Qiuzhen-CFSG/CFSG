module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The unique involution of the quaternion group of order eight

Every element of order two in `QuaternionGroup 2` equals the central element
`a 2`; in particular, any two such elements are equal. This elementary fact
ensures that quaternion automorphisms fix the involution, as used in local
fusion arguments for Alperin–Brauer–Gorenstein, Chapter II, §1, Proposition 1
(article pp. 10–11; `refs/latex/alperin-brauer-gorenstein.tex`).

The proof uses Mathlib's two quaternion normal forms and their order formulas.
An element `xa i` has order four. For `a i`, the order formula reduces to a
kernel-checked calculation on the four elements of `ZMod 4`, leaving only
`i = 2`. No ambient group or subgroup assumptions are required.
-/

namespace QuaternionGroup

/-- The quaternion involution is the element `a 2`. -/
public theorem eq_a_two_of_orderOf_eq_two (x : QuaternionGroup 2)
    (hx : orderOf x = 2) : x = a 2 := by
  cases x with
  | a i =>
    rw [orderOf_a] at hx
    have hi : ∀ j : ZMod (2 * 2), 2 * 2 / Nat.gcd (2 * 2) j.val = 2 → j = 2 := by
      decide
    exact congrArg a (hi i hx)
  | xa i =>
    rw [orderOf_xa] at hx
    exact (by decide : (4 : ℕ) ≠ 2) hx |>.elim

/-- Any two involutions of the quaternion group of order eight are equal. -/
public theorem eq_of_orderOf_eq_two (x y : QuaternionGroup 2)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y :=
  (eq_a_two_of_orderOf_eq_two x hx).trans (eq_a_two_of_orderOf_eq_two y hy).symm

end QuaternionGroup
