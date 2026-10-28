module

public import Theory.Character.BrauerTuanIntersection
public import Mathlib.GroupTheory.Sylow

/-!
# Reduction of mixed-prime intersection divisibility to block orthogonality

If a group has no element of order `p*q`, every `p`-singular element is
`q`-regular. Block column orthogonality at these two primes therefore gives
disjoint kernel supports on every nonidentity element of a Sylow `q`-subgroup.
Character averaging gives an integral quotient by the Sylow order, and hence
by every power of `q` dividing the group order.

The block support hypotheses here are discharged by the localized block
projectors in the final mixed-prime intersection theorem.
Source: Brauer--Tuan, *On simple groups of finite order I* (1945), Lemma 3,
printed pp.764--765, equations (4.8)--(4.13).
-/

public section
noncomputable section
open scoped BigOperators
namespace BrauerTuan
variable {G : Type*} [Group G] [Finite G]

/-- Excluding mixed prime order separates the two singular loci. -/
theorem not_dvd_orderOf_of_no_mixed_order
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hno : ∀ x : G, orderOf x ≠ p * q) (g : G) (hg : p ∣ orderOf g) :
    ¬ q ∣ orderOf g := by
  intro hq
  have hc : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  have hd : p * q ∣ orderOf g := hc.mul_dvd_of_dvd_of_dvd hg hq
  exact hno (g ^ (orderOf g / (p * q)))
    (orderOf_pow_orderOf_div (orderOf_pos g).ne' hd)

/-- Divisibility of denominators descends algebraic-integral quotients. -/
theorem isIntegral_div_of_dvd {z : ℂ} {m n : ℕ}
    (hn : n ≠ 0) (hmn : m ∣ n) (hz : IsIntegral ℤ (z / (n : ℂ))) :
    IsIntegral ℤ (z / (m : ℂ)) := by
  obtain ⟨k, hk⟩ := hmn
  have hm : (m : ℂ) ≠ 0 := by
    exact_mod_cast (fun h : m = 0 => hn (by simp [h] at hk ⊢; exact hk))
  have hk0 : (k : ℂ) ≠ 0 := by
    exact_mod_cast (fun h : k = 0 => hn (by simp [h] at hk ⊢; exact hk))
  have heq : z / (m : ℂ) = (z / (n : ℂ)) * (k : ℂ) := by
    rw [hk, Nat.cast_mul]
    field_simp
  rw [heq]
  exact hz.mul (isIntegral_natCast (R := ℤ) (B := ℂ) k)

/-- The arithmetic and averaging part of the mixed-prime intersection theorem.
The two hypotheses are ordinary block column orthogonality at `p` and `q`. -/
theorem isIntegral_intersection_sum_div_prime_pow_of_orthogonality
    {I : Type*} [Fintype I] [DecidableEq I]
    (χ : I → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (A B : Finset I) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hno : ∀ x : G, orderOf x ≠ p * q)
    (hA : ∀ a b : G, p ∣ orderOf a → ¬ p ∣ orderOf b →
      ∑ i ∈ A, χ i (ConjClasses.mk a) * star (χ i (ConjClasses.mk b)) = 0)
    (hB : ∀ a b : G, q ∣ orderOf a → ¬ q ∣ orderOf b →
      ∑ i ∈ B, χ i (ConjClasses.mk a) * star (χ i (ConjClasses.mk b)) = 0)
    (u : G) (hu : p ∣ orderOf u) (b : ℕ) (hb : q ^ b ∣ Nat.card G) :
    IsIntegral ℤ ((∑ i ∈ A ∩ B,
      χ i (ConjClasses.mk 1) * χ i (ConjClasses.mk u)) / ((q ^ b : ℕ) : ℂ)) := by
  classical
  let Q : Sylow q G := Classical.choice inferInstance
  have hstar (i : I) (g : G) : star (χ i (ConjClasses.mk g⁻¹)) =
      χ i (ConjClasses.mk g) := by
    obtain ⟨n, ρ, hρ⟩ := (hχ.1 i).1
    rw [hρ]
    change star (ρ.character g⁻¹) = ρ.character g
    rw [Representation.representation_character_inv_eq_star_character, star_star]
  have hi := isIntegral_intersection_sum_div_card_of_kernel_support χ hχ A B u
    (Q : Subgroup G) (fun g => p ∣ orderOf g) (fun g hg => hA u g hu hg) (by
      intro x hx g hg
      have hxq : q ∣ orderOf (x : G) := by
        simpa only [Subgroup.orderOf_coe] using Q.isPGroup'.dvd_orderOf hx
      have hgq : ¬ q ∣ orderOf g⁻¹ := by
        simpa only [orderOf_inv] using not_dvd_orderOf_of_no_mixed_order hpq hno g hg
      have hz := hB (x : G) g⁻¹ hxq hgq
      simpa only [hstar, mul_comm] using hz)
  exact isIntegral_div_of_dvd (Nat.card_pos (α := (Q : Subgroup G))).ne'
    (Q.pow_dvd_card_of_pow_dvd_card hb) hi

end BrauerTuan
