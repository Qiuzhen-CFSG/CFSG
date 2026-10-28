module
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Cyclic Sylow control of square conjugacy

Conjugacy into a cyclic subgroup transports a square-conjugating element.
When a prime occurs only once in the group order, Sylow conjugacy places
every element of that prime order in the chosen cyclic subgroup. These
lemmas feed the native M₂₄ prime-order calculation in `PrimeFusion`.
-/

public section
namespace IsConj

/-- For a prime occurring once in the group order, one cyclic subgroup controls fusion. -/
theorem of_order_eq_prime_power_generator
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p)
    (hp : ¬ p * p ∣ Nat.card G) : ∃ n : ℕ, IsConj y (x ^ n) := by
  classical
  let P : Sylow p G :=
    (IsPGroup.of_card (G := Subgroup.zpowers x) (n := 1) (by
      rw [Nat.card_zpowers, hx, pow_one])).toSylow (by
        intro hi
        apply hp
        have hc := (Subgroup.zpowers x).card_mul_index
        rw [Nat.card_zpowers, hx] at hc
        rw [← hc]
        exact Nat.mul_dvd_mul_left p hi)
  obtain ⟨z, hz⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (hy.trans (pow_one p).symm)
  have hm : (z : G) ∈ Subgroup.zpowers x := z.property
  obtain ⟨n, _, hn⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hm)
  exact ⟨n, hn.symm ▸ hz⟩



/-- Square fusion extends to every element conjugate into the same cyclic group. -/
theorem square_of_conjugate_power {G : Type*} [Group G] {x y : G}
    (h : IsConj x (x ^ 2)) (n : ℕ) (hy : IsConj y (x ^ n)) :
    IsConj y (y ^ 2) := by
  have hp : IsConj (x ^ n) ((x ^ n) ^ 2) := by
    simpa only [← pow_mul, Nat.mul_comm 2 n] using IsConj.pow n h
  exact hy.trans (hp.trans (IsConj.pow 2 hy).symm)


end IsConj
