module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power representatives and powers

A coset of a normal subgroup in a finite group contains a p-element exactly
when its image in the quotient is a p-element. A separate power construction
removes the prime-to-p part of an element's order. If the quotient by a
specified subgroup is a p-group, this power preserves nonmembership in it.

These are the elementary replacement steps needed in Aschbacher–Smith,
Corollary A.2.6, printed p.34 of `refs/quasithin.pdf`. The distinction between
staying in the same coset and taking a power is essential. The proofs use
only element orders and coprimality, with no classification hypothesis.
-/

public section
open Subgroup

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- A prime-power element in a coset forces prime-power order of its image. -/
theorem quotient_order_dvd_of_prime_power_coset (N : Subgroup G) [N.Normal]
    (x y : G) (hcoset : QuotientGroup.mk' N y = QuotientGroup.mk' N x)
    (p k : ℕ) (hy : y ^ (p ^ k) = 1) :
    orderOf (QuotientGroup.mk' N x) ∣ p ^ k := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← hcoset, ← map_pow, hy, map_one]

/-- Remove the prime-to-p part of the order by taking a power. -/
theorem exists_primary_power [Finite G] (p : ℕ) (hp : p.Prime) (x : G) :
    ∃ k m : ℕ, Nat.Coprime p m ∧ orderOf (x ^ m) = p ^ k := by
  obtain ⟨k, m, hm, hx⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  have hmpos : 0 < m := by
    have ho := orderOf_pos x
    rw [hx] at ho
    exact Nat.pos_of_mul_pos_left ho
  refine ⟨k, m, hp.coprime_iff_not_dvd.mpr hm, ?_⟩
  rw [orderOf_pow_of_dvd hmpos.ne' (by rw [hx]; exact dvd_mul_left _ _), hx]
  exact Nat.mul_div_cancel _ hmpos

/-- If H/D is a p-group, the p-primary power retains failure of membership in D. -/
theorem exists_primary_power_outside [Finite G] (p : ℕ) [hp : Fact p.Prime]
    (D : Subgroup H) [D.Normal] (hD : IsPGroup p (H ⧸ D))
    (f : G →* H) (x : G) (hx : f x ∉ D) :
    ∃ k m : ℕ, Nat.Coprime p m ∧ orderOf (x ^ m) = p ^ k ∧ f (x ^ m) ∉ D := by
  obtain ⟨k, m, hm, hpow⟩ := exists_primary_power p hp.out x
  refine ⟨k, m, hm, hpow, ?_⟩
  intro hy
  have hc := hD.orderOf_coprime hm (QuotientGroup.mk' D (f x))
  have hd : orderOf (QuotientGroup.mk' D (f x)) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hy
  apply hx
  apply (QuotientGroup.eq_one_iff _).mp
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd)

/-- A finite coset has a p-element precisely when its image is a p-element. -/
theorem exists_prime_power_coset_iff [Finite G] (p : ℕ) (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (x : G) :
    (∃ y : G, QuotientGroup.mk' N y = QuotientGroup.mk' N x ∧
      ∃ a : ℕ, y ^ (p ^ a) = 1) ↔
    ∃ b : ℕ, (QuotientGroup.mk' N x) ^ (p ^ b) = 1 := by
  constructor
  · rintro ⟨y, hy, a, ha⟩
    exact ⟨a, orderOf_dvd_iff_pow_eq_one.mp
      (quotient_order_dvd_of_prime_power_coset N x y hy p a ha)⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, m, hm, ha⟩ := exists_primary_power p hp x
    have hc : Nat.Coprime m (orderOf (QuotientGroup.mk' N x)) :=
      (hm.symm.pow_right b).of_dvd_right (orderOf_dvd_of_pow_eq_one hb)
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hc
    refine ⟨(x ^ m) ^ r, ?_, a, ?_⟩
    · simpa only [map_pow] using hr
    · rw [← ha, ← pow_mul, Nat.mul_comm r, pow_mul, pow_orderOf_eq_one, one_pow]

end Theory.GroupTheory
