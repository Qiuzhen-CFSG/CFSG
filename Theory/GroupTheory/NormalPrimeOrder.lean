module

public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Prime-order elements in normal subgroups

If a prime occurs only once in the order of a finite group, every element of
that prime order belongs to every normal subgroup whose order is divisible by
the prime. Cauchy's theorem supplies an element in the normal subgroup; Sylow
conjugacy carries it into the chosen cyclic subgroup. Normality and the fact
that a nonidentity element generates a group of prime order finish the proof.

This is a standard consequence of the Sylow and Cauchy theorems.
-/

namespace Subgroup
/-- If the square of `p` does not divide the group order, a normal subgroup
whose order is divisible by `p` contains every element of order `p`. -/
public theorem mem_normal_of_prime_order_of_square_not_dvd {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] {p : ℕ} [hp : Fact p.Prime]
    (hN : p ∣ Nat.card N) (r : G) (hr : orderOf r = p)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) : r ∈ N := by
  have hc : Nat.card (zpowers r) = p := (Nat.card_zpowers r).trans hr
  have hi : ¬ p ∣ (zpowers r).index := by
    rintro ⟨k, hk⟩
    apply hsq
    refine ⟨k, ?_⟩
    rw [← (zpowers r).card_mul_index, hc, hk, pow_two, Nat.mul_assoc]
  let P : Sylow p G := (IsPGroup.of_card (p := p) (n := 1) (by simpa using hc)).toSylow hi
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hN
  obtain ⟨y, hxy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (x := (x : G)) (n := 1)
    (by simpa only [Subgroup.orderOf_coe, pow_one] using hx)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hyN : (y : G) ∈ N := hg ▸ (inferInstance : N.Normal).conj_mem x.val x.property g
  have hy : y ≠ 1 := by
    intro he
    have hx1 : (x : G) = 1 := by
      have he' : (y : G) = 1 := congrArg Subtype.val he
      rw [he'] at hg
      have := congrArg (fun z : G => g⁻¹ * z * g) hg
      simpa [mul_assoc] using this
    have : orderOf x = 1 := orderOf_eq_one_iff.mpr (Subtype.ext hx1)
    exact hp.out.ne_one (hx.symm.trans this)
  have hm : (⟨r, mem_zpowers r⟩ : P) ∈ zpowers y :=
    mem_zpowers_of_prime_card hc hy
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
  have hk' := congrArg (fun z : P => (z : G)) hk
  change (y : G) ^ k = r at hk'
  rw [← hk']
  exact N.zpow_mem hyN k
end Subgroup
