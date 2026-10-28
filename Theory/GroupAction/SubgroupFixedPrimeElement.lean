module

public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Fixed prime-order elements in normalized subgroups

If a p-element normalizes a finite subgroup whose order is divisible by p,
its conjugation orbits show that the centralizer also has order divisible
by p. Cauchy's theorem supplies a fixed element of order p. This uses the
literal ambient centralizer and requires no automorphism classification.
-/

public section

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_order_prime_in_centralizer_of_normalizes
    (L : Subgroup G) {x : G} (hx : x ^ p = 1)
    (hn : x ∈ normalizer (L : Set G)) (hd : p ∣ Nat.card L) :
    ∃ a ∈ L, orderOf a = p ∧ a ∈ centralizer ({x} : Set G) := by
  have hp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx)
  have hm := card_modEq_card_inf_centralizer (zpowers x) L hp (zpowers_le.mpr hn)
  have hc : p ∣ Nat.card (L ⊓ centralizer (zpowers x : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp (hm.symm.trans hd.modEq_zero_nat)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hc
  refine ⟨a, a.property.1, (Subgroup.orderOf_coe a).trans ha, ?_⟩
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp a.property.2 x (mem_zpowers x)).symm

end Subgroup
