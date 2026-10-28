module

public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Conjugate-power coverage from local Sylow data

A list that covers the elements of order `p` inside one Sylow subgroup up to
conjugate powers covers all elements of order `p` in the ambient finite group.
If the group order is not divisible by `p²`, any fixed element of order `p`
already suffices. We also give a cardinality-based interface so concrete local
certificates need only supply a subgroup of the full prime-power order.

The proof uses Sylow conjugacy and the fact that every nonidentity element
of a group of prime order generates it. This is a direct consequence of the
Sylow theorems, using `SylowElementConjugacy` and Mathlib's prime-cardinality API.
-/

namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Conjugate-power coverage in a Sylow subgroup transfers to the ambient group. -/
public theorem conjugate_power_coverage_of_local {ι : Type*} (r : ι → G)
    (P : Sylow p G)
    (hlocal : ∀ y : P, orderOf y = p → ∃ i k g, r i = g * (y : G) ^ k * g⁻¹)
    {x : G} (hx : orderOf x = p) : ∃ i k g, r i = g * x ^ k * g⁻¹ := by
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  change (MulAut.conj c) x = (y : G) at hc
  have hyorder : orderOf y = p := by
    rw [← Subgroup.orderOf_coe, ← hc, MulEquiv.orderOf_eq, hx]
  obtain ⟨i, k, g, hi⟩ := hlocal y hyorder
  refine ⟨i, k, g * c, ?_⟩
  have hpow : (y : G) ^ k = c * x ^ k * c⁻¹ := by
    rw [← hc, ← map_pow, MulAut.conj_apply]
  rw [hi, hpow]
  simp only [mul_inv_rev, mul_assoc]

/-- Any element of a prime-order Sylow subgroup is a conjugate of a power of
any ambient element of that prime order. -/
public theorem exists_conjugate_pow_of_prime_card (P : Sylow p G) (hP : Nat.card P = p)
    (r : P) {x : G} (hx : orderOf x = p) :
    ∃ k g, (r : G) = g * x ^ k * g⁻¹ := by
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  change (MulAut.conj g) x = (y : G) at hg
  have hyorder : orderOf y = p := by
    rw [← Subgroup.orderOf_coe, ← hg, MulEquiv.orderOf_eq, hx]
  have hyne : y ≠ 1 := by
    intro h
    have hp := (Fact.out : p.Prime).ne_one
    apply hp
    simpa [h] using hyorder.symm
  obtain ⟨k, hk⟩ := mem_powers_of_prime_card hP hyne (g' := r)
  refine ⟨k, g, ?_⟩
  have hpow : (MulAut.conj g) (x ^ k) = (r : G) := by
    rw [map_pow, hg]
    exact congrArg Subtype.val hk
  exact hpow.symm
end Sylow

/-- When the prime occurs only once in the group order, any two elements
of that order are conjugate up to taking a power. -/
public theorem exists_conjugate_pow_of_orderOf_eq_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : ¬ p ^ 2 ∣ Nat.card G) {r x : G}
    (hr : orderOf r = p) (hx : orderOf x = p) :
    ∃ k g, r = g * x ^ k * g⁻¹ := by
  have hP : IsPGroup p (Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by simpa using hr)
  have hind : ¬ p ∣ (Subgroup.zpowers r).index := by
    intro hd
    apply hcard
    rw [← (Subgroup.zpowers r).card_mul_index, Nat.card_zpowers, hr, pow_two]
    exact Nat.mul_dvd_mul_left p hd
  let P := hP.toSylow hind
  exact P.exists_conjugate_pow_of_prime_card (by simpa [P] using hr)
    ⟨r, Subgroup.mem_zpowers r⟩ hx

namespace Subgroup
/-- A subgroup of full prime-power order suffices for local coverage. -/
public theorem conjugate_power_coverage_of_card
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {ι : Type*} (r : ι → G) (H : Subgroup G)
    (hH : Nat.card H = p ^ n) (hcard : ¬ p ^ (n + 1) ∣ Nat.card G)
    (hlocal : ∀ y : H, orderOf y = p → ∃ i k g, r i = g * (y : G) ^ k * g⁻¹)
    {x : G} (hx : orderOf x = p) : ∃ i k g, r i = g * x ^ k * g⁻¹ := by
  have hP : IsPGroup p H := IsPGroup.of_card hH
  have hind : ¬ p ∣ H.index := by
    intro hd
    apply hcard
    rw [← H.card_mul_index, hH, pow_succ]
    exact Nat.mul_dvd_mul_left (p ^ n) hd
  exact (hP.toSylow hind).conjugate_power_coverage_of_local r hlocal hx
end Subgroup
