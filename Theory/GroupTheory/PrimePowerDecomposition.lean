module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Nat.Factorization.Basic
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Cyclic prime-power decomposition through coprime kernels

Split a finite-order element inside its cyclic subgroup into commuting
prime-power and prime-to-prime parts. Homomorphisms with coprime kernels
preserve the order of the prime-power part.

The decomposition proof is adapted from `NormalizedCoprimeCoset` in this
repository. These elementary facts support the section calculation in
Alperin–Brauer–Gorenstein III.7, equation (8), pp.103–104.
-/

open Subgroup

/-- The commuting prime-power and prime-to-prime parts lie in the original cyclic subgroup. -/
public theorem exists_prime_power_decomposition {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (g : G) :
    ∃ u v : G, (∃ k : ℕ, u ^ (p ^ k) = 1) ∧
      Nat.Coprime p (orderOf v) ∧ Commute u v ∧ u * v = g ∧
      u ∈ zpowers g ∧ v ∈ zpowers g := by
  obtain ⟨k, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hmpos : 0 < m := by
    have := orderOf_pos g
    rw [hn] at this
    exact Nat.pos_of_mul_pos_left this
  have hord : orderOf (g ^ m) = p ^ k := by
    rw [orderOf_pow_of_dvd hmpos.ne' (by rw [hn]; exact dvd_mul_left _ _), hn]
    exact Nat.mul_div_cancel _ hmpos
  have hcop : Nat.Coprime m (orderOf (g ^ m)) := by
    rw [hord]
    exact (hp.coprime_iff_not_dvd.mpr hm).symm.pow_right k
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  let u := (g ^ m) ^ b
  let v := u⁻¹ * g
  have hum : u ^ m = g ^ m := by
    simpa only [u, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb
  have hug : Commute u g := (Commute.refl g).pow_left m |>.pow_left b
  have hvm : v ^ m = 1 := by
    rw [hug.inv_left.mul_pow, inv_pow, hum, inv_mul_cancel]
  refine ⟨u, v, ⟨k, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · change ((g ^ m) ^ b) ^ (p ^ k) = 1
    rw [← pow_mul, Nat.mul_comm b, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  · exact (hp.coprime_iff_not_dvd.mpr hm).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hvm)
  · exact (Commute.refl u).inv_right.mul_right hug
  · exact mul_inv_cancel_left u g
  · exact (zpowers g).pow_mem ((zpowers g).pow_mem (mem_zpowers g) m) b
  · exact (zpowers g).mul_mem ((zpowers g).inv_mem
      ((zpowers g).pow_mem ((zpowers g).pow_mem (mem_zpowers g) m) b)) (mem_zpowers g)

/-- Coprime kernels preserve the order of every prime-power-order element. -/
public theorem MonoidHom.orderOf_eq_of_prime_power_of_coprime_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker)) (g : G)
    (hg : ∃ k : ℕ, g ^ (p ^ k) = 1) : orderOf (f g) = orderOf g := by
  obtain ⟨k, hk⟩ := hg
  have hP : IsPGroup p (zpowers g) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hi := injective_comp_subtype_of_coprime_ker f hker (zpowers g) hP
  exact (orderOf_injective (f.comp (zpowers g).subtype) hi ⟨g, mem_zpowers g⟩).trans
    (Subgroup.orderOf_coe ⟨g, mem_zpowers g⟩).symm
