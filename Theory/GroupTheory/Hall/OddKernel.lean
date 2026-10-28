module
public import Theory.GroupTheory.Hall.Basic
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Mathlib.GroupTheory.Index

/-!
# Kernels containing an odd Hall subgroup

The order of an element's image divides both its original order and the
index of every subgroup in the kernel. An odd Hall index is coprime to
every odd order, so a homomorphism killing that Hall subgroup kills every
odd-order element. No solvability or Hall conjugacy is needed.

Source application: propagation of the original component field-kernel
calculation across its Sylow exchanger in Aschbacher--Smith 10.2.3, p.745.
-/

public section
namespace Subgroup.OddHall
open Subgroup
variable {A Q : Type*} [Group A] [Group Q]

theorem map_eq_one_of_odd_order_of_hall_le_ker
    (E : Subgroup A) (hE : IsHallSubgroup oddPrimes E)
    (f : A →* Q) (hEf : E ≤ f.ker) (a : A) (ha : Odd (orderOf a)) : f a = 1 := by
  have hc : Nat.Coprime (orderOf a) E.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpa hpE
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hpa)
    exact hE.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpE hp2
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc (orderOf_map_dvd f a)
  have hr : f a ∈ f.range := ⟨a,rfl⟩
  have hd : orderOf (f a) ∣ Nat.card f.range := by
    simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨f a,hr⟩ : f.range)
  rw [←index_ker] at hd
  exact hd.trans (index_dvd_of_le hEf)
end Subgroup.OddHall
