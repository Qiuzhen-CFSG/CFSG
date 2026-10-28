module

public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Theory.SpecificGroups.Tits.RelativeSylowMarking
public import Theory.SpecificGroups.Tits.SharpOuterBound

/-!
# An order-based two-rank estimate for Tits automorphisms

The certified Sylow subgroup has order 2^11 and is nonabelian: its center
certificate excludes normal form 1. Every elementary subgroup is therefore
proper, giving intrinsic two-rank at most 10. Centerlessness and an outer
group of order at most two then give automorphism two-rank at most 11.

This is weaker than the source's bound 5, but suffices for the degree-26
comparison since 2*(11+1) < 26. The final theorems discharge the outer-order
premise using the certified compatible local count in SharpOuterBound.
The actual Parrott–Atlas equivalence transports the intrinsic
calculation. No identification with the full ReeF4.Model 0 is used.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.356; GLS3, Section 2.5; Parrott (1972), Section 5, p.683, as transcribed in
refs/original/n-group-global/parrott-tits-presentation.md.
-/

public section

open Subgroup Theory.GroupTheory
namespace Tits.AutomorphismTwoRank

open scoped IsMulCommutative

/-- The concrete Sylow subgroup is nonabelian, by its certified center. -/
theorem sylow_two_noncommutative : ¬ IsMulCommutative atlas1600SylowTwoSubgroup := by
  intro h
  let := h
  have hc : atlas1600SylowTwoEquiv 1 ∈ center atlas1600SylowTwoSubgroup := by
    rw [center_eq_top]
    exact mem_top _
  have hzero : atlas1600SylowTwoNormalForm 0 = 1 := by
    norm_num [atlas1600SylowTwoNormalForm_eq]
  have h65 : atlas1600SylowTwoNormalForm 65 = atlas1600R5 := by
    norm_num [atlas1600SylowTwoNormalForm_eq, atlas1600R5_eq]
  rcases (atlas1600SylowTwo_mem_center_iff _).mp hc with he | he
  · have he' : atlas1600SylowTwoNormalForm 1 = atlas1600SylowTwoNormalForm 0 := by
      simpa only [atlas1600SylowTwoEquiv_apply] using he.trans hzero.symm
    have := atlas1600SylowTwoNormalForm_injective he'
    norm_num at this
  · have he' : atlas1600SylowTwoNormalForm 1 = atlas1600SylowTwoNormalForm 65 := by
      simpa only [atlas1600SylowTwoEquiv_apply] using he.trans h65.symm
    exact (by decide : (1 : Fin 2048) ≠ 65)
      (atlas1600SylowTwoNormalForm_injective he')

/-- Properness of elementary subgroups saves one from the Sylow order bound. -/
theorem atlas_two_rank_le_ten :
    primeRank 2 Atlas1600Group ≤ 10 := by
  rw [atlas1600SylowTwo.primeRank_eq, atlas1600SylowTwo_coe]
  apply primeRank_le_of_noncommutative_card_prime_pow
  · norm_num [atlas1600SylowTwoSubgroup_card]
  · exact sylow_two_noncommutative

/-- The intrinsic estimate on the actual presented simple Tits carrier. -/
theorem parrott_two_rank_le_ten : primeRank 2 ParrottGroup ≤ 10 := by
  rw [primeRank_equiv 2 parrottFiniteImageEquiv]
  exact atlas_two_rank_le_ten

/-- The sharp outer-order bound gives a sufficient automorphism rank estimate. -/
theorem automorphism_two_rank_le_of_outer_card
    (houter : Nat.card (MulAut.Outer ParrottGroup) ≤ 2) :
    primeRank 2 (MulAut ParrottGroup) ≤ 11 := by
  have h := automorphism_primeRank_le_add_of_outer_card (p := 2) (n := 1)
    (RelativeSylowMarking.center_eq_bot parrottFiniteImageEquiv)
    (by simpa using houter)
  have hr := parrott_two_rank_le_ten
  omega

/-- The order-based estimate is strictly below the degree-26 threshold. -/
theorem automorphism_two_rank_degree_gap_of_outer_card
    (houter : Nat.card (MulAut.Outer ParrottGroup) ≤ 2) :
    2 * (primeRank 2 (MulAut ParrottGroup) + 1) < 26 := by
  have h := automorphism_two_rank_le_of_outer_card houter
  omega

/-- The full automorphism group of the simple Parrott carrier has two-rank
at most eleven, with the sharp outer-order premise discharged. -/
theorem automorphism_two_rank_le : primeRank 2 (MulAut ParrottGroup) ≤ 11 :=
  automorphism_two_rank_le_of_outer_card SharpOuterBound.parrott_outer_card_le_two

/-- The unconditional bound excludes the degree-26 simple derived endpoint. -/
theorem automorphism_two_rank_degree_gap :
    2 * (primeRank 2 (MulAut ParrottGroup) + 1) < 26 := by
  have h := automorphism_two_rank_le
  omega

end Tits.AutomorphismTwoRank
