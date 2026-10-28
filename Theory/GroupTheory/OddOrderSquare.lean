module
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Squares of elements of odd order

Two elements of odd order in an arbitrary group are equal if their squares
are equal. The elements need not belong to a common odd-order subgroup,
and neither ambient finiteness nor commutativity is assumed.

This supplies the square-root transfer in Brauer, *On finite Desarguesian
planes I*, proof of (2D), article page 120. There the roots lie in a root
subgroup and a conjugate of a different root subgroup, so injectivity of
squaring inside either subgroup alone does not suffice.

The product of the two element orders is an odd common annihilating exponent
`2 * k + 1`. Raising each square to `k + 1` recovers its original element,
which proves injectivity across the two cyclic subgroups.
-/

namespace Theory.GroupTheory

/-- Equality of squares determines elements of odd order, even in different
odd-order subgroups of an arbitrary group. -/
public theorem eq_of_sq_eq_sq_of_odd_orderOf
    {G : Type*} [Group G] {a b : G} (ha : Odd (orderOf a))
    (hb : Odd (orderOf b)) (hs : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨k, hk⟩ := ha.mul hb
  have hexp : 2 * (k + 1) = orderOf a * orderOf b + 1 := by omega
  have ha' : (a ^ 2) ^ (k + 1) = a := by
    rw [← pow_mul, hexp, pow_succ, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  have hb' : (b ^ 2) ^ (k + 1) = b := by
    rw [← pow_mul, hexp, pow_succ, pow_mul', pow_orderOf_eq_one, one_pow, one_mul]
  exact ha'.symm.trans ((congrArg (fun z : G => z ^ (k + 1)) hs).trans hb')

end Theory.GroupTheory
