module
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.Quasithin.LocalRank

/-!
# Cubic local rank in binary SL₃

The upper-unitriangular Sylow subgroup is nontrivial and its full normalizer
contains the two-parameter diagonal torus. In even binary field degree each
parameter contributes a cubic direction. The ordinary rank bound therefore
identifies the rank of this literal normalizer and the two-local rank as two.

Source: Aschbacher--Smith, A.2.12(I.i), printed pp.36--37. This argument uses
the actual unipotent two-subgroup, including in characteristic two where the
embedded SL₂ has trivial center.
-/

open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.ThreeCoverLocalRanks

/-- The actual binary SL₃ Sylow normalizer has cubic rank two in even degree. -/
public theorem binary_linear_normalizer_threeRank_eq_two
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    primeRank 3 (normalizer (unipotentSL F : Set SL(3,F))) = 2 := by
  apply le_antisymm
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 _
      (normalizer (unipotentSL F : Set SL(3,F))).subtype_injective).trans
      (binary_linear_special_threeRank_eq_two hcard hn).le
  · have hr : 1 ≤ primeRank 3 Fˣ := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      rw [Nat.card_units, hcard]
      exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr hn
    have hprod : 2 ≤ primeRank 3 (Fˣ × Fˣ) := by
      rw [primeRank_prod_eq_add]
      omega
    have htorus : 2 ≤ primeRank 3 (torusSL F).range := by
      rwa [← Theory.GroupTheory.primeRank_equiv 3 (torusSLEquiv F)]
    rw [normalizer_unipotentSL]
    exact htorus.trans (Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion (torusSL_le_borel F)) (inclusion_injective _))

/-- The nontrivial root Sylow is the literal two-local cubic-rank witness. -/
public theorem binary_linear_twoLocal_witness
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hnpos : 0 < n) (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    ∃ R : Subgroup SL(3,F), R ≠ ⊥ ∧ IsPGroup 2 R ∧
      primeRank 3 (normalizer (R : Set SL(3,F))) = 2 := by
  refine ⟨unipotentSL F, ?_, ?_, binary_linear_normalizer_threeRank_eq_two hcard hn⟩
  · intro he
    have hc := card_unipotentSL F
    rw [he, card_bot, hcard] at hc
    have hp : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
    have hp3 : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow (by decide) hp
    omega
  · apply IsPGroup.of_card (n := n * 3)
    rw [card_unipotentSL, hcard, pow_mul]

/-- The binary linear cover has exact local cubic rank two. -/
public theorem binary_linear_twoLocalPrimeRank_eq_two
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hnpos : 0 < n) (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    twoLocalPrimeRank 3 SL(3,F) = 2 := by
  apply le_antisymm
  · exact (twoLocalPrimeRank_le_primeRank 3).trans
      (binary_linear_special_threeRank_eq_two hcard hn).le
  · obtain ⟨R, hR, hRp, hr⟩ := binary_linear_twoLocal_witness hnpos hcard hn
    have hlocal : IsTwoLocal (normalizer (R : Set SL(3,F))) := ⟨R, hR, hRp, rfl⟩
    exact hr.ge.trans (hlocal.primeRank_le 3)
end Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
