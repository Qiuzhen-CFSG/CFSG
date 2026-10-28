module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex

/-!
# The source order divides the literal J₄ matrix-group order

Lagrange's theorem for the certified max1 subgroup and the order-1331 subgroup,
together with four certified prime-order words, gives the source order as their
least common multiple. The independently proved ambient two-part makes the
quotient odd. Thus an upper bound below three source orders forces equality.

Source: the ATLAS `J4G1-f2r112B0` representation and word certificates cited in
`Cardinality.LocalOrder`, `PrimeCoverage.Elevens`, and `PrimeCoverage.WordOrders`.
The source factorization is
`2^21 * 3^3 * 5 * 7 * 11^3 * 23 * 29 * 31 * 37 * 43`.
-/

public section
namespace Janko4.Cardinality.Thompson
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

/-- The least common multiple of actual subgroup and element orders is the source order. -/
theorem source_order_dvd_model_card : 86775571046077562880 ∣ Nat.card Model := by
  have hM : 501397585920 ∣ Nat.card Model := by
    simpa only [max1Subgroup_card] using
      (max1Subgroup matrixA_mul_self matrixB_pow_four).card_subgroup_dvd_card
  have h11 : 1331 ∣ Nat.card Model := by
    simpa only [Simplicity.Elevens.local_card] using
      (Simplicity.Elevens.localSubgroup matrixA_mul_self matrixB_pow_four).card_subgroup_dvd_card
  have h29 : 29 ∣ Nat.card Model := by
    rw [← Simplicity.orderOf_primeRepresentative_twentyNine matrixA_mul_self matrixB_pow_four]
    exact orderOf_dvd_natCard _
  have h31 : 31 ∣ Nat.card Model := by
    rw [← Simplicity.orderOf_primeRepresentative_thirtyOne matrixA_mul_self matrixB_pow_four]
    exact orderOf_dvd_natCard _
  have h37 : 37 ∣ Nat.card Model := by
    rw [← Simplicity.orderOf_primeRepresentative_thirtySeven matrixA_mul_self matrixB_pow_four]
    exact orderOf_dvd_natCard _
  have h43 : 43 ∣ Nat.card Model := by
    rw [← Simplicity.orderOf_primeRepresentative_fortyThree matrixA_mul_self matrixB_pow_four]
    exact orderOf_dvd_natCard _
  have h := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd
    (Nat.lcm_dvd hM h11) h29) h31) h37) h43
  norm_num at h
  exact h

/-- A positive odd multiple below three times the source order equals that order. -/
theorem model_card_eq_of_thompson_bound
    (hbound : Nat.card Model < 3 * 86775571046077562880) :
    Nat.card Model = 86775571046077562880 := by
  obtain ⟨q, hq⟩ := source_order_dvd_model_card
  have hpos := Nat.card_pos (α := Model)
  have htwo := OuterReduction.OddIndex.model_two_part_bound
  have hqodd : ¬ 2 ∣ q := by
    intro hd
    apply htwo
    rw [hq]
    obtain ⟨k, rfl⟩ := hd
    exact ⟨41377816699065 * k, by ring⟩
  have hq1 : q = 1 := by omega
  simpa only [hq1, mul_one] using hq

end Janko4.Cardinality.Thompson
