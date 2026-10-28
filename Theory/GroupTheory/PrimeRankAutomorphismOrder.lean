module

public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Automorphism prime rank from Sylow and outer orders

Inner elementary subgroups have orders dividing the original group order.
Its Sylow subgroup therefore controls their rank, without any assumption on
the conjugation kernel. For a centerless group, a small outer quotient gives
an additive bound instead. Noncommutativity saves one dimension from the
order bound because each elementary subgroup is proper.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
printed p.356, and the inner/outer conventions of GLS3, Section 2.5.
These elementary estimates do not assert automorphism classification.
-/

public section

open Subgroup
namespace Theory.GroupTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]

/-- An order bound bounds elementary rank. -/
theorem primeRank_le_of_card_le_prime_pow (hcard : Nat.card G ≤ p ^ n) :
    primeRank p G ≤ n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E _
  exact (Subgroup.card_le_card_group E).trans hcard

/-- Noncommutativity saves one from the bound furnished by a prime-power order. -/
theorem primeRank_le_of_noncommutative_card_prime_pow
    (hcard : Nat.card G = p ^ (n + 1)) (hna : ¬ IsMulCommutative G) :
    primeRank p G ≤ n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  have hproper : E ≠ ⊤ := by
    intro he
    apply hna
    exact IsMulCommutative.of_comm fun x y => by
      have hx : x ∈ E := he ▸ mem_top x
      have hy : y ∈ E := he ▸ mem_top y
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
  have hlt : Nat.card E < Nat.card G := by
    apply lt_of_le_of_ne (Subgroup.card_le_card_group E)
    exact fun h => hproper (E.eq_top_of_card_eq h)
  rw [ha, hcard] at hlt
  have he : a ≤ n := by
    have := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hlt
    omega
  rw [ha]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos he

/-- Innerness of all elements killed by p controls automorphism rank through
the order of an actual Sylow subgroup, even when G has nontrivial center. -/
theorem automorphism_primeRank_le_of_prime_order_inner (P : Sylow p G)
    (hcard : Nat.card P ≤ p ^ n)
    (hinner : ∀ a : MulAut G, a ^ p = 1 → a ∈ MulAut.innerSubgroup G) :
    primeRank p (MulAut G) ≤ n := by
  apply (primeRank_le_iff_elementary_card_le (MulAut G)).mpr
  intro E hE
  let := hE
  have hle : E ≤ MulAut.innerSubgroup G := by
    intro a ha
    exact hinner a (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hd : Nat.card E ∣ Nat.card G :=
    (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd MulAut.conj)
  obtain ⟨e, he⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
  have hdP : Nat.card E ∣ Nat.card P := by
    rw [he] at hd ⊢
    exact P.pow_dvd_card_of_pow_dvd_card hd
  exact (Nat.le_of_dvd Nat.card_pos hdP).trans hcard

/-- In a centerless finite group, a small outer quotient adds at most n
to the intrinsic prime rank. -/
theorem automorphism_primeRank_le_add_of_outer_card (hz : center G = ⊥)
    (houter : Nat.card (MulAut.Outer G) ≤ p ^ n) :
    primeRank p (MulAut G) ≤ primeRank p G + n := by
  have hf : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (MulAut.conj : G →* MulAut G).ker.eq_bot_iff_forall.mpr
    intro x hx
    have hx' : MulAut.conj x = 1 := hx
    have hc : x ∈ center G := by
      rw [mem_center_iff]
      intro y
      have hy := MulEquiv.congr_fun hx' y
      change x * y * x⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    simpa only [hz, mem_bot] using hc
  let e : G ≃* MulAut.innerSubgroup G := MonoidHom.ofInjective hf
  have h := primeRank_le_add_of_index_le (MulAut.innerSubgroup G) houter
  rw [← Theory.GroupTheory.primeRank_equiv p e] at h
  exact h

end Theory.GroupTheory
