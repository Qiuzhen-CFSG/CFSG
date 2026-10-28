module

public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.UnitaryCentralProduct
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRanks
public import Theory.GroupTheory.CubicProductRankFour.LocalReplacement
public import Theory.SpecificGroups.SU3.CentralCubeLocalRelocation

/-!
# Actual source applications for the unitary central product

The proved signed degree-three local ranks discharge the factor hypotheses
in the exceptional product calculation. Quasithinness therefore forces the
binary field degrees to have greatest common divisor one or three; the
original components give the literal exceptional pair in Theorem A. Central
cube-root extraction and relocation supply the missing two-local contradiction
for a hypothetical rank-four elementary subgroup, proving exact three-rank.
The quotient rank bound uses the actual scalar projection, retaining its model
parameters and original field.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section

open Subgroup
private theorem center_le_of_card_three {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card (center A) = 3) (z : A) (hz : z ∈ center A) (hz1 : z ≠ 1)
    (C : Subgroup A) (hzC : z ∈ C) : center A ≤ C := by
  have hz3 : z ^ 3 = 1 := by
    have hh := (pow_card_eq_one' (x := (⟨z, hz⟩ : center A)))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have he : zpowers z = center A := eq_of_le_of_card_ge (zpowers_le.mpr hz) (by
    rw [Nat.card_zpowers, hord, hcard])
  rw [← he]
  exact zpowers_le.mpr hzC


namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The actual scalar quotient has the source three-rank bound. -/
theorem special_unitary_quotient_threeRank_le_two {n : ℕ} (hn : 3 ≤ n)
    (h : IsSpecialUnitaryModel H 3 (2 ^ n)) : primeRank 3 (H ⧸ center H) ≤ 2 := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := h
  obtain ⟨q, _⟩ := exists_special_centerQuotient_equiv J (by omega) hcard hc e
  exact unitary_odd_primeRank_le_two Nat.prime_three (by decide)
    ⟨F, inferInstance, inferInstance, J, hcard, hc, ⟨q⟩⟩

/-- The source arithmetic conclusion with both factor ranks proved. -/
theorem UnitaryCentralProductData.source_gcd_eq
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H) :
    Nat.gcd d.n₁ d.n₂ = 1 ∨ Nat.gcd d.n₁ d.n₂ = 3 := by
  apply d.gcd_eq hH
  · intro p hp hp3 hd
    exact (unitary_binary_special_rank_pair (by have := d.first_large; omega)
      hp (hp.odd_of_ne_two (by omega)) hd d.first_model).2.ge
  · intro p hp hp3 hd
    exact (unitary_binary_special_rank_pair (by have := d.second_large; omega)
      hp (hp.odd_of_ne_two (by omega)) hd d.second_model).1.ge

/-- The original components satisfy the actual exceptional Theorem A alternative. -/
noncomputable def UnitaryCentralProductData.source_TheoremAUnitaryPair
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H)
    (hfirst : IsComponent H d.first) (hsecond : IsComponent H d.second) :
    TheoremAUnitaryPair H where
  first := d.first
  second := d.second
  first_component := hfirst
  second_component := hsecond
  product := d.product
  n₁ := d.n₁
  n₂ := d.n₂
  first_large := d.first_large
  second_large := d.second_large
  first_odd := d.first_odd
  second_odd := d.second_odd
  first_model := d.first_model
  second_model := d.second_model
  centers_eq := d.centers_eq
  gcd_eq := d.source_gcd_eq hH

/-- Exact rank three, with the central-cube localization constructed in SU₃. -/
theorem UnitaryCentralProductData.source_threeRank_eq_three
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H) : primeRank 3 H = 3 := by
  apply le_antisymm _ d.three_le_primeRank
  apply CubicProductRankFour.primeRank_le_three_of_cubic_localization d.first d.second
    d.commuting d.product d.centers_eq d.intersection_eq
    d.factor_centers_card.1 d.factor_centers_card.2
    (unitary_special_threeRank_eq_two (by have := d.first_large; omega) d.first_odd d.first_model).le
    (unitary_special_threeRank_eq_two (by have := d.second_large; omega) d.second_odd d.second_model).le
    (special_unitary_quotient_threeRank_le_two d.first_large d.first_model)
    (special_unitary_quotient_threeRank_le_two d.second_large d.second_model) _ hH
  intro z x hz hz1 hx
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := d.first_model
  obtain ⟨Q, C, hQ, hp, hC, hCc, hzC, hCN⟩ :=
    HermitianForm.CentralCubeLocalRelocation.exists_local_cyclic_nine_of_equiv
      J d.first_large d.first_odd hcard hc e z hz hz1 x hx
  exact ⟨Q, C, hp, hQ, hC, hCc, center_le_of_card_three d.factor_centers_card.1 z hz hz1 C hzC, hCN⟩

/-- Both numerical conclusions of the exceptional source calculation. -/
theorem UnitaryCentralProductData.source_rank_and_gcd
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H) :
    primeRank 3 H = 3 ∧ (Nat.gcd d.n₁ d.n₂ = 1 ∨ Nat.gcd d.n₁ d.n₂ = 3) :=
  ⟨d.source_threeRank_eq_three hH, d.source_gcd_eq hH⟩
end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
