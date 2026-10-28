module

import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M22.Basic
public import Theory.Mathieu.M22.Properties.Identification
public import Theory.Mathieu.M22.Properties.OrderCertificate
public import Theory.Mathieu.M22.Properties.OrderLevel0
public import Theory.Mathieu.M22.Properties.OrderLevel1
public import Theory.Mathieu.M22.Properties.OrderLevel2
public import Theory.Mathieu.M22.Properties.OrderLevel3
public import Theory.Mathieu.M22.Properties.OrderLevel4

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

private theorem m22Generated_order :
    Nat.card (wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec) = 443520 := by
  rw [m22L0_card, m22L1_card, m22L2_card, m22L3_card, m22L4_card, m22L5_card]

private theorem m22GeneratorA_mem_m22Atlas : m22GeneratorA ∈ m22Atlas := by
  rw [m22Atlas_eq_closure]
  exact Subgroup.subset_closure (by simp)

private theorem m22GeneratorB_mem_m22Atlas : m22GeneratorB ∈ m22Atlas := by
  rw [m22Atlas_eq_closure]
  exact Subgroup.subset_closure (by simp)

private theorem m22Generated_le_m22Atlas :
    wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec ≤ m22Atlas := by
  intro g hg
  rcases hg with ⟨w, rfl⟩
  induction w with
  | nil => exact m22Atlas.one_mem
  | cons i w ih =>
      apply m22Atlas.mul_mem
      · fin_cases i
        · change m22L0G0 ∈ m22Atlas
          rw [← m22GeneratorA_eq_m22L0G0]
          exact m22GeneratorA_mem_m22Atlas
        · change m22L0G1 ∈ m22Atlas
          rw [← m22GeneratorB_eq_m22L0G1]
          exact m22GeneratorB_mem_m22Atlas
        · change m22L0G0⁻¹ ∈ m22Atlas
          rw [← m22GeneratorA_eq_m22L0G0]
          exact m22Atlas.inv_mem m22GeneratorA_mem_m22Atlas
        · change m22L0G1⁻¹ ∈ m22Atlas
          rw [← m22GeneratorB_eq_m22L0G1]
          exact m22Atlas.inv_mem m22GeneratorB_mem_m22Atlas
      · exact ih

private theorem m22Atlas_le_m22Generated :
    m22Atlas ≤ wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec := by
  rw [m22Atlas_eq_closure, Subgroup.closure_le]
  intro g hg
  rcases hg with (rfl | rfl)
  · rw [m22GeneratorA_eq_m22L0G0]
    simpa [evalWord, m22L0Gen] using
      (evalWord_mem_wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec
        [(0 : Fin 4)])
  · rw [m22GeneratorB_eq_m22L0G1]
    simpa [evalWord, m22L0Gen] using
      (evalWord_mem_wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec
        [(1 : Fin 4)])

private theorem m22Generated_eq_m22Atlas :
    wordSubgroup m22L0Gen m22L0Inv m22L0Inv_spec = m22Atlas :=
  le_antisymm m22Generated_le_m22Atlas m22Atlas_le_m22Generated

/-- The Atlas-generated computational subgroup has order 443520. -/
public theorem m22Atlas_order : Nat.card m22Atlas = 443520 := by
  rw [← m22Generated_eq_m22Atlas]
  exact m22Generated_order

/-- The Atlas computational subgroup is exactly the even Steiner automorphism group. -/
public theorem m22Atlas_eq_M22 : m22Atlas = M22 := by
  apply Subgroup.eq_of_le_of_card_ge m22Atlas_le_M22
  rw [m22Atlas_order]
  exact m22_order_upper_bound

/-- The standard Steiner-defined Mathieu group M22 has order 443520. -/
public theorem m22_order : Nat.card M22 = 443520 := by
  rw [← m22Atlas_eq_M22]
  exact m22Atlas_order

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise


public theorem m22_order_factorization :
    Nat.card M22 = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 := by
  rw [m22_order]
  norm_num

/-- The prime divisors of the order of `M22` are exactly `2`, `3`, `5`, `7`, and `11`. -/
public theorem m22_prime_dvd_order_iff (p : ℕ) [Fact (Nat.Prime p)] :
    p ∣ Nat.card M22 ↔ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  rw [m22_order,
    show 443520 = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 * 11 by norm_num]
  have hp : Nat.Prime p := Fact.out
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 11)]
  aesop

/-- The prime spectrum of `M22`. -/
public theorem m22_prime_spectrum :
    Nat.primeFactors (Nat.card M22) = {2, 3, 5, 7, 11} := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    let : Fact (Nat.Prime p) := ⟨hp⟩
    exact (m22_prime_dvd_order_iff p).mp hdiv
  · intro h
    rw [m22_order]
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by norm_num, by norm_num⟩

end Sporadic.Mathieu
