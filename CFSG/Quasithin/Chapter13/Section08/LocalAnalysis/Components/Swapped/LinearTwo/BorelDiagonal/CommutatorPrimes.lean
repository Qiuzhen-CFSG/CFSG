module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel

public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The prime divisors of the source commutator [B,s]

Since B₀ normalizes L and s lies in L, [B,s] lies in L. Since s normalizes
B₀, it also lies in B₀. The source line normalization therefore puts it in
M₁ = N_LT(V₁). The literal definition L₁ = O²(M₁), together with the
three-group quotient of L₁ above its two-core, makes every prime divisor
of M₁ either two or three. This works before the parameter n is determined.

Normality is relative: the source supplies B₀ ≤ M ≤ N_G(L), not ambient
normality of L. Source: Aschbacher–Smith, Notation 12.2.5 and 13.2.1,
printed pp.796,877, and proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G] [Finite G]

/-- A two-by-three group has only the indicated prime divisors. -/
theorem primes_of_two_core_three_quotient (D : Subgroup G)
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card D) : p = 2 ∨ p = 3 := by
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  obtain ⟨b, hb⟩ := hq.exists_card_eq
  have hc := (pCore 2 D).card_mul_index
  rw [index_eq_card, ha, hb] at hc
  rw [← hc] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)

/-- Adjoining the two-quotient above O²(M₁) introduces no other primes. -/
theorem parabolic_primes_of_marked_quotient (M₁ L₁ : Subgroup G)
    (hdef : L₁ = (pResidual 2 M₁).map M₁.subtype)
    (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁)) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card M₁) : p = 2 ∨ p = 3 := by
  obtain ⟨a, ha⟩ := (isPGroup_quotient_pResidual (G := M₁) 2).exists_card_eq
  have hc := (pResidual 2 M₁).card_mul_index
  rw [index_eq_card, ha] at hc
  have hcard : Nat.card L₁ = Nat.card (pResidual 2 M₁) := by
    rw [hdef, card_map_of_injective M₁.subtype_injective]
  rw [← hc, ← hcard] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact primes_of_two_core_three_quotient L₁ hq hp h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)

omit [Finite G] in
/-- The actual commutator lies in N_LT(V₁). Only relative normalization of
L and B₀ is used. -/
theorem commutator_le_marked_parabolic (L T V₁ B₀ B : Subgroup G) {s : G}
    (hB : B ≤ B₀) (hBL : B₀ ≤ normalizer (L : Set G))
    (hBV : B₀ ≤ normalizer (V₁ : Set G))
    (hsL : s ∈ L) (hsB : s ∈ normalizer (B₀ : Set G)) :
    ⁅B, zpowers s⁆ ≤ (L ⊔ T) ⊓ normalizer (V₁ : Set G) := by
  have hCB : ⁅B, zpowers s⁆ ≤ B₀ :=
    (commutator_mono hB le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hsB))
  have hCL : ⁅B, zpowers s⁆ ≤ L :=
    (commutator_mono le_rfl (zpowers_le.mpr hsL)).trans
      (le_normalizer_iff_commutator_le_right.mp (hB.trans hBL))
  exact le_inf (hCL.trans le_sup_left) (hCB.trans hBV)

/-- Source parabolic structure supplies the {2,3} restriction on [B,s].
This applies in particular to B = O²(B₀), without presupposing n = 2. -/
theorem commutator_primes_of_source_parabolic (L L₁ T V₁ B₀ B : Subgroup G) {s : G}
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (hq : IsPGroup 3 (L₁ ⧸ pCore 2 L₁))
    (hB : B ≤ B₀) (hBL : B₀ ≤ normalizer (L : Set G))
    (hBV : B₀ ≤ normalizer (V₁ : Set G))
    (hsL : s ∈ L) (hsB : s ∈ normalizer (B₀ : Set G)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (⁅B, zpowers s⁆ : Subgroup G) → p = 2 ∨ p = 3 := by
  intro p hp hd
  exact parabolic_primes_of_marked_quotient _ L₁ hdef hq hp
    (hd.trans (card_dvd_of_le (commutator_le_marked_parabolic L T V₁ B₀ B hB hBL hBV hsL hsB)))

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
