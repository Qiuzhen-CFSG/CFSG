module

public import Theory.GroupAction.CoprimeTwoOuter

/-!
# Coprime automorphisms with an inner power

If a power of an automorphism is inner and its order is coprime to that
power, the automorphism itself is inner. Coprimality with the group order
then makes it trivial. The argument uses the full quotient Aut(Q)/Inn(Q),
without a simplicity or automorphism-coverage assumption.

Source application: the odd-prime degree-three rows in Aschbacher--Smith
11.5.6(3), printed p.781; their outer exponent divides six.
-/

public section
open Subgroup
namespace MulAut
variable {Q : Type*} [Group Q]
/-- An inner power coprime to the actor order detects a coprime automorphism. -/
theorem eq_one_of_coprime_of_inner_power (a : MulAut Q) {n : ℕ}
    (hn : Nat.Coprime (orderOf a) n) (hc : Nat.Coprime (orderOf a) (Nat.card Q))
    (hinner : a ^ n ∈ innerSubgroup Q) : a = 1 := by
  let q := QuotientGroup.mk' (innerSubgroup Q)
  have hq : q a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hn (orderOf_map_dvd q a)
    exact orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hinner)
  obtain ⟨x,hx⟩ := (QuotientGroup.eq_one_iff a).mp hq
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc dvd_rfl
  rw [← hx]
  exact (orderOf_map_dvd MulAut.conj x).trans (orderOf_dvd_natCard x)
end MulAut
