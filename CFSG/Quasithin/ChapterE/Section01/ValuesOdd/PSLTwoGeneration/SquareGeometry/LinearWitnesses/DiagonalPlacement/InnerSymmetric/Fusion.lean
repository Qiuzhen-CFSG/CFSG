module

public import GorensteinWalter.GWLemma21Trichotomy
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
import Mathlib.Tactic

/-!
# Cubic normalizer elements from dihedral fusion

For a finite simple group of order greater than four with dihedral Sylow
two-subgroups, Gorenstein–Walter I, Lemma 2.1 puts every four-group in its
first fusion case. The normalizer action then has an element whose square
is nontrivial. Since the automorphism group of a four-group has order six,
three divides the actual normalizer order; Cauchy's theorem supplies a cubic.

This discharges the cubic premise used to recognize the inner S₄ witnesses
in Aschbacher–Smith E.1.14(6), printed p.214 (citing Asc82a, Lemma 4.10).
It uses neither a matrix-element premise nor conjugacy of four-groups.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
namespace DiagonalPlacement.InnerSymmetric.Fusion
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_of_strict (B : Subgroup G) [IsKleinFour B]
    (h : NormalizerContainsCPrime B) :
    ∃ x : normalizer (B : Set G), orderOf x = 3 := by
  classical
  have he : ∃ n : G, n ∈ normalizer (B : Set G) ∧
      n ^ 2 ∉ centralizer (B : Set G) := by
    by_contra! hn
    exact h.2 fun x hx => ⟨hx, hn x hx⟩
  obtain ⟨n, hn, hn2⟩ := he
  let x : normalizer (B : Set G) := ⟨n, hn⟩
  let φ : MulAut B := B.normalizerMonoidHom x
  have hφ : φ ^ 2 ≠ 1 := by
    intro hsq
    have hker : x ^ 2 ∈ B.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hsq
    rw [normalizerMonoidHom_ker] at hker
    exact hn2 hker
  have hd : orderOf φ ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using orderOf_dvd_natCard φ
  have h3 : 3 ∣ orderOf φ := by
    have hcases : ∀ d ∈ Nat.divisors 6, d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by decide
    rcases hcases _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) with h1 | h2 | h3 | h6
    · exact (hφ ((orderOf_dvd_iff_pow_eq_one).mp (by rw [h1]; decide))).elim
    · exact (hφ ((orderOf_dvd_iff_pow_eq_one).mp (by rw [h2]))).elim
    · rw [h3]
    · rw [h6]; decide
  exact exists_prime_orderOf_dvd_card' 3
    (h3.trans ((orderOf_map_dvd B.normalizerMonoidHom x).trans (orderOf_dvd_natCard x)))

/-- Fusion in a simple group with dihedral Sylow two-subgroups supplies an
actual cubic element in each four-group normalizer. -/
theorem exists_order_three_of_simple_dihedral [IsSimpleGroup G]
    (hdihedral : HasDihedralSylowTwo G) (hlarge : 4 < Nat.card G)
    (T : Sylow 2 G) (B : Subgroup G) (hB : IsKleinFour B) (hBT : B ≤ T) :
    ∃ x : normalizer (B : Set G), orderOf x = 3 := by
  have hno (n : ℕ) (hn : n = 2 ∨ n = 4) :
      ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = n := by
    rintro ⟨N, hN, hi⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN with rfl | rfl
    · rw [index_bot] at hi
      omega
    · rw [index_top] at hi
      omega
  rcases gw_lemma_2_1 hdihedral with h | h | h
  · let := hB
    exact cubic_of_strict B (h.2.2 T B hBT hB)
  · exact (hno 2 (Or.inl rfl) h.1).elim
  · exact (hno 4 (Or.inr rfl) h.1).elim
end DiagonalPlacement.InnerSymmetric.Fusion
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
