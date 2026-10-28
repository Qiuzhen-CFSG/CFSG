module

public import Mathlib.GroupTheory.Sylow

/-!
# Cyclic coverage of elements of prime order

Sylow conjugacy reduces coverage by powers and conjugates to a single Sylow
subgroup. When the group order is not divisible by the square of the prime,
one element of that order suffices.

The proofs are adapted from the existing general lemmas in
`Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction`,
without importing that concrete matrix model. Its public API is preserved.
-/

@[expose] public section

namespace PrimeCyclicCoverage

open scoped Pointwise

/-- If the group order contains only one factor of `p`, its elements of order
`p` generate conjugate cyclic subgroups. -/
theorem exists_conjugate_pow_of_prime_sq_not_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsq : ¬p ^ 2 ∣ Nat.card G) {x r : G}
    (hx : orderOf x = p) (hr : orderOf r = p) :
    ∃ (k : ℕ) (g : G), r = g * x ^ k * g⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  have sylow (y : G) (hy : orderOf y = p) :
      ∃ P : Sylow p G, (P : Subgroup G) = Subgroup.zpowers y := by
    have hc : Nat.card (Subgroup.zpowers y) = p := (Nat.card_zpowers y).trans hy
    have hi : ¬p ∣ (Subgroup.zpowers y).index := by
      intro hi
      apply hsq
      rw [← (Subgroup.zpowers y).card_mul_index, hc, pow_two]
      exact Nat.mul_dvd_mul_left p hi
    exact ⟨(IsPGroup.of_card (hc.trans (pow_one p).symm)).toSylow hi, rfl⟩
  obtain ⟨P, hP⟩ := sylow x hx
  obtain ⟨Q, hQ⟩ := sylow r hr
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hrQ : r ∈ Q := by
    change r ∈ (Q : Subgroup G)
    rw [hQ]
    exact Subgroup.mem_zpowers r
  rw [← hg] at hrQ
  change r ∈ (↑(g • P) : Set G) at hrQ
  rw [Sylow.coe_smul] at hrQ
  obtain ⟨y, hy, hyr⟩ := hrQ
  have hyx : y ∈ Subgroup.zpowers x := hP ▸ hy
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff y x).mp
    (mem_powers_iff_mem_zpowers.mpr hyx)
  change g * y * g⁻¹ = r at hyr
  exact ⟨k, g, by rw [hk]; exact hyr.symm⟩

/-- To cover all elements of prime order `p`, it suffices to cover those in one
Sylow `p`-subgroup. The conjugating elements may belong to the whole group. -/
theorem prime_cyclic_coverage_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {ι : Type*} (r : ι → G) (P : Sylow p G)
    (hlocal : ∀ y : G, y ∈ P → orderOf y = p →
      ∃ i k g, r i = g * y ^ k * g⁻¹) :
    ∀ x : G, orderOf x = p → ∃ i k g, r i = g * x ^ k * g⁻¹ := by
  intro x hx
  have hc : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    simp [Nat.card_zpowers, hx]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hc).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hmem : g * x * g⁻¹ ∈ P := by
    rw [← hg]
    change g * x * g⁻¹ ∈ (↑(g • Q) : Set G)
    rw [Sylow.coe_smul]
    exact ⟨x, hQ (Subgroup.mem_zpowers x), rfl⟩
  have hord : orderOf (g * x * g⁻¹) = p :=
    (MulEquiv.orderOf_eq (MulAut.conj g) x).trans hx
  obtain ⟨i, k, h, hi⟩ := hlocal _ hmem hord
  refine ⟨i, k, h * g, ?_⟩
  rw [conj_pow] at hi
  simpa only [mul_inv_rev, mul_assoc] using hi

/-- Coverage by powers and conjugates for elements of a fixed order. -/
def CoversPrime {G : Type*} [Group G] {ι : Type*} (r : ι → G) (p : ℕ) : Prop :=
  ∀ x : G, orderOf x = p → ∃ i k g, r i = g * x ^ k * g⁻¹


end PrimeCyclicCoverage
