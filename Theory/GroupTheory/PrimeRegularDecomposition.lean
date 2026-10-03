module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Commuting prime and prime-regular parts

Every element of a finite group is a product of a commuting element of
prime-power order and an element of order prime to that prime. Factor the
original order as `p^k * m`. Powering by `p^k` is invertible on the cyclic
subgroup of order `m`, giving a prime-regular power with the same `p^k`-th
power as the original element. Dividing by this power gives the prime part.

This elementary primary decomposition is used to pass from two-elements to
two-sections in Brauer, *Some applications of the theory of blocks of
characters of finite groups II* (1964), §IV, Proposition 4, p.313.
-/

public section

/-- A finite-group element splits into commuting prime-power and prime-to-prime parts. -/
theorem exists_commuting_prime_parts {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (g : G) :
    ∃ t v : G, (∃ k : ℕ, t ^ (p ^ k) = 1) ∧
      ¬ p ∣ orderOf v ∧ Commute t v ∧ t * v = g := by
  obtain ⟨k, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have horder : orderOf (g ^ (p ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by rw [hn]; exact dvd_mul_right _ _), hn]
    exact Nat.mul_div_cancel_left m (pow_pos hp.pos _)
  have hcop : (p ^ k).Coprime (orderOf (g ^ (p ^ k))) := by
    rw [horder]
    exact (hp.coprime_iff_not_dvd.mpr hm).pow_left k
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  let v := g ^ (p ^ k * b)
  have hreg : ¬ p ∣ orderOf v := by
    intro hd
    apply hm
    dsimp [v] at hd
    rw [pow_mul] at hd
    exact hd.trans ((orderOf_pow_dvd b).trans (horder ▸ dvd_refl _))
  have hpow : g ^ (p ^ k) = v ^ (p ^ k) := by
    simpa only [v, ← pow_mul, Nat.mul_assoc, Nat.mul_comm b (p ^ k)] using hb.symm
  have hcomm : Commute g v := (Commute.refl g).pow_right _
  refine ⟨g * v⁻¹, v, ⟨k, ?_⟩, hreg, hcomm.mul_left (Commute.refl v).inv_left, ?_⟩
  · rw [hcomm.inv_right.mul_pow, inv_pow, hpow, mul_inv_cancel]
  · simp
