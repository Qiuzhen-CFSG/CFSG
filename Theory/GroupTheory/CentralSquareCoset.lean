module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.Basic
/-!
# An order-four representative in a central-square coset

A commuting factor with square z switches the two possible squares 1 and z.
One of y and y*a therefore has order four and square z. Membership in a
subgroup F containing a separates the entire coset when y lies outside F.

This is the order-four transfer representative in Aschbacher--Smith 2.4.29,
printed p.546.
-/
public section
open Subgroup

/-- A commuting order-four factor switches the two possible central squares. -/
theorem exists_order_four_central_square_outside
    {G : Type*} [Group G] (T F : Subgroup G)
    (y a z : G) (hyT:y∈T) (haT:a∈T) (hyF:y∉F) (haF:a∈F)
    (hy2:y^2=1 ∨ y^2=z) (ha2:a^2=z) (hz2:orderOf z=2)
    (hc:y*a=a*y) :
    ∃j∈T, orderOf j=4 ∧ j^2=z ∧ j∉F := by
  have hz1:z≠1 := by intro hh;rw[hh,orderOf_one] at hz2;omega
  have hzsq:z^2=1 := by rw [←hz2];exact pow_orderOf_eq_one z
  have hord (j:G) (hj:j^2=z):orderOf j=4 := by
    apply orderOf_eq_prime_pow (p:=2) (n:=1)
    · simpa using hj.trans_ne hz1
    · calc
        j^(2^(1+1))=(j^2)^2 := by change j^(2*2)=(j^2)^2;exact pow_mul j 2 2
        _=1 := by rw [hj,hzsq]
  rcases hy2 with hh | hh
  · refine ⟨y*a,T.mul_mem hyT haT,hord _ ?_,?_,?_⟩
    · rw [(show Commute y a from hc).mul_pow,hh,ha2,one_mul]
    · rw [(show Commute y a from hc).mul_pow,hh,ha2,one_mul]
    · intro hya
      apply hyF
      simpa only [mul_inv_cancel_right] using F.mul_mem hya (F.inv_mem haF)
  · exact ⟨y,hyT,hord y hh,hh,hyF⟩
