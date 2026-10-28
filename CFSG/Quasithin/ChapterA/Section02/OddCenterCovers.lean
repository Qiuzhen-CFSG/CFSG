module

public import Theory.SpecificGroups.PSU3.EvenOddCenterCover
public import Theory.SpecificGroups.PSU3.PrimeOddCenterCover
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Concrete odd-center restrictions in A.2.12 and A.2.18

Binary linear and unitary covers are recognized using their scalar projections,
including the exceptional linear field orders two and four.
The dimension-three projective matrix theorem supplies three-rank at most
two for both PSL₃ and PSU₃. Thus Remark A.2.14 excludes the nontrivial
linear and unitary covers in the characteristic-two minimal-counterexample argument.
Only that earlier-source rank-failure implication remains explicit in the
last theorem; the cover recognition and matrix rank bounds are proved.

These results do not yet prove the local SU₃ ranks or the central-product
calculation needed in A.2.12. The parameter 2ⁿ is always the fixed-field
order, so unitary matrices have coefficient field of order (2ⁿ)².

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.12(I–II),
A.2.14 and A.2.18, printed pp.36–37 and 40.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G]

private theorem three_ne_zero_of_binary_card
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    (3 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  change (↑(3 : ℕ) : F) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff F 2]
  norm_num

/-- The actual binary PSL₃ model has three-rank at most two. -/
theorem linear_threeRank_le_two {n : ℕ}
    (h : ClassicalGroup.IsPSL G 3 (2 ^ n)) : primeRank 3 G ≤ 2 := by
  obtain ⟨F, _, _, hcard, ⟨j⟩⟩ := h
  rw [primeRank_equiv 3 j]
  exact Matrix.ProjectiveDimensionThree.psl_primeRank_three_le_two
    (three_ne_zero_of_binary_card hcard)

/-- The actual binary PSU₃ model has three-rank at most two, including
every Hermitian form with the prescribed Frobenius involution. -/
theorem unitary_threeRank_le_two {n : ℕ}
    (h : ClassicalGroup.IsPSU G 3 (2 ^ n)) : primeRank 3 G ≤ 2 := by
  obtain ⟨F, _, _, J, hcard, _hc, ⟨j⟩⟩ := h
  rw [primeRank_equiv 3 j]
  exact Matrix.ProjectiveDimensionThree.psu_primeRank_three_le_two
    (three_ne_zero_of_binary_card (n := n * 2)
      (by simpa only [pow_mul, Nat.mul_comm] using hcard)) J

/-- The unitary quotient in A.2.12(I.ii) has three-rank exactly two.
The lower bound uses the actual diagonal/cycle elementary subgroup. -/
theorem unitary_threeRank_eq_two {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (h : ClassicalGroup.IsPSU G 3 (2 ^ n)) : primeRank 3 G = 2 := by
  apply le_antisymm (unitary_threeRank_le_two h)
  obtain ⟨F, _, _, J, hcard, hc, ⟨j⟩⟩ := h
  rw [primeRank_equiv 3 j]
  exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective
    J hn hcard hc hodd

/-- The corresponding exact rank for the split cubic-center parameters. -/
theorem linear_threeRank_eq_two {n : ℕ} (hodd : Even n)
    (h : ClassicalGroup.IsPSL G 3 (2 ^ n)) : primeRank 3 G = 2 := by
  apply le_antisymm (linear_threeRank_le_two h)
  obtain ⟨F, _, _, hcard, ⟨j⟩⟩ := h
  rw [primeRank_equiv 3 j]
  exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hcard hodd

/-- A binary unitary central quotient forces the original odd center to
divide gcd(3,2ⁿ+1); no multiplier premise remains. -/
theorem unitary_center_card_dvd [IsQuasisimple G] {n : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ n))
    (ho : Odd (Nat.card (center G))) :
    Nat.card (center G) ∣ Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨j⟩⟩ := h
  exact HermitianForm.EvenOddCenterCover.center_card_dvd J hn hcard hc j ho

/-- The nontrivial binary unitary cover in A.2.12(I) is SU₃(2ⁿ),
with odd n ≥ 3 and an actual cyclic center of order three. -/
theorem unitary_nontrivial_center [IsQuasisimple G] {n : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ n))
    (ho : Odd (Nat.card (center G))) (hz : center G ≠ ⊥) :
    Odd n ∧ 3 ≤ n ∧ Nat.card (center G) = 3 ∧
      Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧
      IsSpecialUnitaryModel G 3 (2 ^ n) := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨j⟩⟩ := h
  obtain ⟨hnodd, hn3, h3, hZ, k, _hk⟩ :=
    HermitianForm.EvenOddCenterCover.nontrivial_center_recognition J hn hcard hc j ho hz
  exact ⟨hnodd, hn3, h3, hZ, F, inferInstance, inferInstance, J, hcard, hc, ⟨k.symm⟩⟩

/-- The odd-prime unitary branch of A.2.12(I), recognized on the actual
special unitary carrier rather than by its center order alone. -/
theorem odd_prime_unitary_nontrivial_center [IsQuasisimple G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ClassicalGroup.IsPSU (G ⧸ center G) 3 p)
    (ho : Odd (Nat.card (center G))) (hz : center G ≠ ⊥) :
    p % 3 = 2 ∧ Nat.card (center G) = 3 ∧
      Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧
      IsSpecialUnitaryModel G 3 p := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨j⟩⟩ := h
  obtain ⟨hm, h3, hZ, k, _hk⟩ :=
    HermitianForm.PrimeOddCenterCover.nontrivial_center_recognition J hp hp2 hcard hc j ho hz
  exact ⟨hm, h3, hZ, F, inferInstance, inferInstance, J, hcard, hc, ⟨k.symm⟩⟩

omit [Finite G] in
/-- At the ordinary binary parameters, the linear cover has scalar center.
The two exceptional field orders are handled separately in the source. -/
theorem linear_center_card_dvd [IsQuasisimple G] {n : ℕ} (hn : 3 ≤ n)
    (h : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ n)) :
    Nat.card (center G) ∣ Nat.gcd 3 (2 ^ n - 1) := by
  obtain ⟨F, _, _, hcard, ⟨j⟩⟩ := h
  have h8 : 8 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  simpa only [hcard] using Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
    (by omega : Nat.card F ≠ 2) (by omega : Nat.card F ≠ 4) j

/-- The linear counterpart of the A.2.14 application at ordinary parameters. -/
theorem linear_center_eq_bot_of_a214 [IsQuasisimple G] {n : ℕ} (hn : 3 ≤ n)
    (h : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ n))
    (hA214 : Nat.card (center G) = 3 → 2 < primeRank 3 (G ⧸ center G)) :
    center G = ⊥ := by
  by_contra hz
  have hd := (linear_center_card_dvd hn h).trans (Nat.gcd_dvd_left 3 (2 ^ n - 1))
  have h3 : Nat.card (center G) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact (hz ((center G).eq_bot_of_card_eq h1)).elim
    · exact h3
  exact (not_lt_of_ge (linear_threeRank_le_two h)) (hA214 h3)

/-- The linear center bound for every positive binary field degree,
including the exceptional multiplier at q = 4 and the PSL₂(7) endpoint. -/
theorem binary_linear_center_card_dvd [IsQuasisimple G] {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ n))
    (ho : Odd (Nat.card (center G))) : Nat.card (center G) ∣ 3 := by
  by_cases hn3 : 3 ≤ n
  · exact (linear_center_card_dvd hn3 h).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨F, _, _, hcard, ⟨j⟩⟩ := h
  interval_cases n
  · have hz := Matrix.PSL3.BinaryOddCenterCover.center_eq_bot_two
      (by simpa using hcard) j ho
    simp [hz]
  · exact Matrix.PSL3.BinaryOddCenterCover.center_card_dvd_three_four
      (by simpa using hcard) j ho

/-- All binary linear odd-center cases satisfy the exclusion required in
A.2.18 once the earlier A.2.14 rank-failure implication is supplied. -/
theorem binary_linear_center_eq_bot_of_a214 [IsQuasisimple G] {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL (G ⧸ center G) 3 (2 ^ n))
    (ho : Odd (Nat.card (center G)))
    (hA214 : Nat.card (center G) = 3 → 2 < primeRank 3 (G ⧸ center G)) :
    center G = ⊥ := by
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ (binary_linear_center_card_dvd hn h ho)
    with h1 | h3
  · exact (center G).eq_bot_of_card_eq h1
  · exact ((not_lt_of_ge (linear_threeRank_le_two h)) (hA214 h3)).elim

/-- Application to the literal quotient in A.2.18: the earlier A.2.14
rank-failure implication rules out a nontrivial center. Its producer is
the A.2 minimal-counterexample reduction, not a matrix-model assumption. -/
theorem unitary_center_eq_bot_of_a214 [IsQuasisimple G] {n : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ n))
    (ho : Odd (Nat.card (center G)))
    (hA214 : Nat.card (center G) = 3 → 2 < primeRank 3 (G ⧸ center G)) :
    center G = ⊥ := by
  by_contra hz
  obtain ⟨_, _, h3, _, _⟩ := unitary_nontrivial_center hn h ho hz
  exact (not_lt_of_ge (unitary_threeRank_le_two h)) (hA214 h3)

end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
