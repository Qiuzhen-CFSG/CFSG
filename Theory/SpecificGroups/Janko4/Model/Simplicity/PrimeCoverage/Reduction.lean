module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.Words
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.FinCases

/-!
# Sylow reductions for cyclic coverage in the binary J₄ model

The proposed order factors as
`2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43`.
For each prime occurring only once, every subgroup of that prime order is a
Sylow subgroup. Sylow conjugacy therefore reduces cyclic coverage to checking
the order of one specified word. For 2, 3 and 11 we retain explicit local
coverage obligations; a second Sylow argument allows checking each obligation
inside one concrete Sylow subgroup.

The word indices and proposed order come from the ATLAS entry
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ . All arithmetic and Sylow
reductions here are proved; the ATLAS class table is not assumed. The theorem
`prime_cyclic_coverage_of_local` is conditional on the seven word orders and
three remaining local coverage results, as well as the model order.
-/

@[expose] public section

namespace Janko4.Simplicity

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

/-- The complete list of prime divisors of the proposed model order. -/
theorem prime_dvd_model_order {p : ℕ} (hp : p.Prime) (hd : p ∣ 86775571046077562880) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 ∨
      p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43 := by
  have hf : 86775571046077562880 =
      2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by norm_num
  rw [hf] at hd
  simpa only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43), or_assoc] using hd

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

/-- The prime factors that occur only once in the proposed model order. -/
def singlePrime : Fin 7 → ℕ := ![5, 7, 23, 29, 31, 37, 43]

/-- Indices of the corresponding words in `primeRepresentative`. -/
def singlePrimeIndex : Fin 7 → Fin 12 := ![3, 4, 7, 8, 9, 10, 11]

/-- Every entry of the single-factor table is prime. -/
theorem singlePrime_prime (j : Fin 7) : (singlePrime j).Prime := by
  fin_cases j <;> decide

/-- None of the squares of these primes divides the proposed model order. -/
theorem singlePrime_sq_not_dvd (j : Fin 7) :
    ¬singlePrime j ^ 2 ∣ 86775571046077562880 := by
  fin_cases j <;> decide

/-- Only three local coverage results and seven word-order certificates remain. -/
theorem prime_cyclic_coverage_of_local
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (horders : ∀ j : Fin 7,
      orderOf (primeRepresentative (a hA) (b hB) (singlePrimeIndex j)) = singlePrime j)
    (h2 : CoversPrime (primeRepresentative (a hA) (b hB)) 2)
    (h3 : CoversPrime (primeRepresentative (a hA) (b hB)) 3)
    (h11 : CoversPrime (primeRepresentative (a hA) (b hB)) 11) :
    ∀ x : Model, (orderOf x).Prime →
      ∃ (i : Fin 12) (k : ℕ) (g : Model),
        primeRepresentative (a hA) (b hB) i = g * x ^ k * g⁻¹ := by
  intro x hx
  have hd : orderOf x ∣ 86775571046077562880 := hcard ▸ orderOf_dvd_natCard x
  have hs (j : Fin 7) (hj : orderOf x = singlePrime j) :
      ∃ (i : Fin 12) (k : ℕ) (g : Model),
        primeRepresentative (a hA) (b hB) i = g * x ^ k * g⁻¹ := by
    obtain ⟨k, g, heq⟩ := exists_conjugate_pow_of_prime_sq_not_dvd
      (singlePrime_prime j) (hcard ▸ singlePrime_sq_not_dvd j) hj (horders j)
    exact ⟨singlePrimeIndex j, k, g, heq⟩
  rcases prime_dvd_model_order hx hd with h | h | h | h | h | h | h | h | h | h
  · exact h2 x h
  · exact h3 x h
  · exact hs 0 h
  · exact hs 1 h
  · exact h11 x h
  · exact hs 2 h
  · exact hs 3 h
  · exact hs 4 h
  · exact hs 5 h
  · exact hs 6 h

end Janko4.Simplicity
