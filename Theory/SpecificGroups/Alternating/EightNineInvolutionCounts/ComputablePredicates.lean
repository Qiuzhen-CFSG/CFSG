module
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.Basic

/-!
# Efficient checked predicates for involutions and product orders

For a nonempty product of transpositions, cycle type is determined by the
involution equation and the size of the support. A finite order certificate
checks the defining power and every smaller positive power. These structural
lemmas avoid repeated cycle factorization in finite table certificates.
-/

namespace alternatingGroup.EightNineInvolutionCounts
open Equiv Equiv.Perm
open Theory.GroupTheory.TwoInvolutionClassOrder

public theorem cycleType_replicate_two_iff {α : Type*} [Fintype α] [DecidableEq α]
    (p : Perm α) {k : ℕ} (hk : 0 < k) :
    p.cycleType = Multiset.replicate k 2 ↔ p * p = 1 ∧ p.support.card = 2 * k := by
  constructor
  · intro h
    constructor
    · have ho : orderOf p ∣ 2 := by
        rw [← lcm_cycleType, h, Multiset.lcm_dvd]
        intro n hn
        have he : n = 2 := (Multiset.mem_replicate.mp hn).2
        exact he ▸ dvd_rfl
      simpa only [pow_two] using (orderOf_dvd_iff_pow_eq_one.mp ho)
    · rw [← sum_cycleType, h]
      simp [Nat.mul_comm]
  · rintro ⟨hp, hs⟩
    have hne : p ≠ 1 := by
      intro he
      simp only [he, support_one, Finset.card_empty] at hs
      omega
    have ho : orderOf p = 2 := orderOf_eq_prime (by simpa only [pow_two] using hp) hne
    obtain ⟨j, hj⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
    rw [ho] at hj
    have he := p.sum_cycleType
    rw [hj, hs] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    have hjk : j + 1 = k := by omega
    simpa only [hjk] using hj

public theorem orderOf_eq_of_finite_check {G : Type*} [Monoid G] (g : G) (n : ℕ)
    (hn : 0 < n) (hpow : g ^ n = 1)
    (hmin : ∀ m : Fin n, 0 < m.val → g ^ m.val ≠ 1) : orderOf g = n := by
  apply (orderOf_eq_iff hn).mpr
  exact ⟨hpow, fun m hm hp => hmin ⟨m, hm⟩ hp⟩

public theorem halfOrder_eq_iff_of_order {α : Type*} [Fintype α] [DecidableEq α]
    (a b u : alternatingGroup α) (n : ℕ)
    (hn : orderOf ((a : Perm α) * (b : Perm α)) = n) :
    halfOrder a b = u ↔ ((a : Perm α) * (b : Perm α)) ^ (n / 2) = (u : Perm α) := by
  rw [halfOrder_eq_iff, lcm_cycleType, hn]

end alternatingGroup.EightNineInvolutionCounts
