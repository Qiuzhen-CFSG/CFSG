module

public import Theory.GroupTheory.SubgroupConjugation

/-!
# Conjugation by prime-order subgroups

If two subgroups have the same prime order and one normalizes the other,
then it centralizes it. The conjugation action is trivial by the existing
p-group action theorem: a cyclic group of order p has p−1 automorphisms.

If an element whose odd power is one moves a subgroup, its first three
successive conjugates are distinct. Equality of successive conjugates
cancels. Equality of the first and third would make the square fix the
subgroup; the element is a power of its square, so it too would fix it.

These are the elementary conjugation inputs to the normalizer argument in
Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(1–2),
printed pp.183–184. They require no assumptions about action supports.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Two subgroups of the same prime order centralize one another whenever the
second normalizes the first. -/
public theorem le_centralizer_of_prime_card_of_le_normalizer [Finite G] (X Y : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hX : Nat.card X = p) (hY : Nat.card Y = p)
    (hYX : Y ≤ normalizer (X : Set G)) : Y ≤ centralizer (X : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Normalizes Y X := ⟨hYX⟩
  have hYp : IsPGroup p Y := IsPGroup.of_card (n := 1) (by simpa using hY)
  have htriv := actsTrivially_of_isPGroup_on_cyclic_prime_order
    (A := Y) (G := X) hp hYp (isCyclic_of_prime_card hX) hX
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  have heq := congrArg Subtype.val (htriv (⟨y, hy⟩ : Y) (⟨x, hx⟩ : X))
  change y * x * y⁻¹ = x at heq
  have hcomm := congrArg (fun z : G => z * y) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcomm.symm

/-- An element annihilated by an odd power has at least three distinct successive
conjugates of any subgroup that it moves. No finiteness assumption is needed. -/
public theorem conjBy_three_pairwise_ne_of_odd_pow_eq_one (H : Subgroup G) {g : G} {n : ℕ}
    (hn : Odd n) (hg : g ^ n = 1) (hmove : H.conjBy g ≠ H) :
    H ≠ H.conjBy g ∧ H ≠ (H.conjBy g).conjBy g ∧
      H.conjBy g ≠ (H.conjBy g).conjBy g := by
  refine ⟨Ne.symm hmove, ?_, ?_⟩
  · intro htwo
    have hfix : H.conjBy (g ^ 2) = H := by
      simpa only [conjBy_conjBy, pow_two] using htwo.symm
    have hfixpow : ∀ k : ℕ, H.conjBy ((g ^ 2) ^ k) = H := by
      intro k
      induction k with
      | zero => simp only [pow_zero, conjBy_one]
      | succ k ih => rw [pow_succ, conjBy_mul, hfix, ih]
    obtain ⟨k, hk⟩ := hn
    have hexp : 2 * (k + 1) = n + 1 := by omega
    have hroot : (g ^ 2) ^ (k + 1) = g := by
      rw [← pow_mul, hexp, pow_succ, hg, one_mul]
    exact hmove (hroot ▸ hfixpow (k + 1))
  · intro heq
    have hcancel := congrArg (fun K : Subgroup G => K.conjBy g⁻¹) heq
    rw [conjBy_inv, conjBy_inv] at hcancel
    exact hmove hcancel.symm

/-- The three-conjugate distinctness criterion for an odd prime exponent. -/
public theorem conjBy_three_pairwise_ne_of_prime_pow_eq_one (H : Subgroup G) {g : G} {p : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hg : g ^ p = 1)
    (hmove : H.conjBy g ≠ H) :
    H ≠ H.conjBy g ∧ H ≠ (H.conjBy g).conjBy g ∧
      H.conjBy g ≠ (H.conjBy g).conjBy g :=
  conjBy_three_pairwise_ne_of_odd_pow_eq_one H (hp.odd_of_ne_two hpodd) hg hmove

/-- An element of an odd-prime-order subgroup has three distinct successive
conjugates of every subgroup that it moves. -/
public theorem conjBy_three_pairwise_ne_of_mem_prime_card (H Y : Subgroup G) {g : G} {p : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hY : Nat.card Y = p)
    (hg : g ∈ Y) (hmove : H.conjBy g ≠ H) :
    H ≠ H.conjBy g ∧ H ≠ (H.conjBy g).conjBy g ∧
      H.conjBy g ≠ (H.conjBy g).conjBy g := by
  apply conjBy_three_pairwise_ne_of_prime_pow_eq_one H hp hpodd _ hmove
  have hpow := congrArg Subtype.val (pow_card_eq_one' (x := (⟨g, hg⟩ : Y)))
  simpa only [hY, Subgroup.coe_pow, OneMemClass.coe_one] using hpow

end Subgroup
