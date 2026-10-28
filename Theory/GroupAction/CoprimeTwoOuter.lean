module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Odd coprime actors with two-group outer image

An odd-order automorphism has trivial image in a two-group outer quotient.
It is therefore inner, and coprimality with the group order kills it.
The quotient is the full automorphism group modulo actual conjugations;
neither simplicity nor a chosen automorphism presentation is required.

Source application: the small outer-group rows in Aschbacher--Smith
11.5.6(3), printed p.781, using A.3.15, pp.50--51.
-/

public section
open Subgroup
namespace MulAut
variable {Q : Type*} [Group Q]

/-- Odd coprime automorphisms vanish when the full outer group is a two-group. -/
theorem eq_one_of_odd_coprime_of_outer_two (a : MulAut Q)
    (ho : Odd (orderOf a)) (hc : Nat.Coprime (orderOf a) (Nat.card Q))
    (houter : IsPGroup 2 (MulAut.Outer Q)) : a = 1 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Q)
  obtain ⟨k,hk⟩ := houter (q a)
  have hq : q a = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right k)
      (orderOf_map_dvd q a) (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨x,hx⟩ := (QuotientGroup.eq_one_iff a).mp hq
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc dvd_rfl
  rw [← hx]
  exact (orderOf_map_dvd MulAut.conj x).trans (orderOf_dvd_natCard x)

end MulAut
