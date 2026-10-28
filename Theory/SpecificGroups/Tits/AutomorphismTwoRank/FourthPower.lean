module

public import Theory.SpecificGroups.Tits.AutomorphismTwoRank
public import Theory.GroupTheory.TwoRankFourthPower

/-!
# A fourth-power improvement of the Tits automorphism rank bound

The certified Sylow subgroup has order 2^11. Its normal form 257 is the
literal Parrott word s1*s7, whose fourth power moves point 0 to point 3.
Consequently no elementary subgroup has index one or two, and the intrinsic
two-rank is at most nine. The proved outer-order bound adds at most one.
This estimate is sufficient for comparison with the Frobenius degree bound 24.

Sources: Parrott (1972), p.683, with the inverse point-map convention of
`Tits.Atlas1600ParrottData`; Aschbacher–Smith G.9.3, printed p.356.
-/

public section
open Subgroup Theory.GroupTheory
namespace Tits.AutomorphismTwoRank.FourthPower

/-- The actual Sylow normal form s1*s7 has nontrivial fourth power. -/
theorem sylow_word_fourth_ne_one :
    atlas1600SylowTwoNormalForm 257 ^ 4 ≠ 1 := by
  have hp : ((Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.s7Perm) ^ 4)
      (0 : Fin 1600) ≠ 0 := by decide +kernel
  intro h
  have he := congrArg (fun x : Atlas1600Group => x.val (0 : Fin 1600)) h
  have hv : (atlas1600SylowTwoNormalForm 257).val =
      Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.s7Perm := by
    norm_num [atlas1600SylowTwoNormalForm_val]
  have hvpow : (atlas1600SylowTwoNormalForm 257 ^ 4).val =
      (atlas1600SylowTwoNormalForm 257).val ^ 4 := rfl
  rw [hvpow, hv] at he
  exact hp he

/-- The fourth-power witness saves two from the Sylow order exponent. -/
theorem atlas_two_rank_le_nine : primeRank 2 Atlas1600Group ≤ 9 := by
  rw [atlas1600SylowTwo.primeRank_eq, atlas1600SylowTwo_coe]
  let x : atlas1600SylowTwoSubgroup :=
    ⟨atlas1600SylowTwoNormalForm 257, atlas1600SylowTwoNormalForm_mem 257⟩
  apply twoRank_le_of_card_pow_and_fourth_ne 9
    (by norm_num [atlas1600SylowTwoSubgroup_card]) x
  intro h
  exact sylow_word_fourth_ne_one (congrArg Subtype.val h)

/-- Transport the bound through the certified Parrott–Atlas equivalence. -/
theorem parrott_two_rank_le_nine : primeRank 2 ParrottGroup ≤ 9 := by
  rw [primeRank_equiv 2 parrottFiniteImageEquiv]
  exact atlas_two_rank_le_nine

/-- The actual automorphism group has two-rank at most ten. -/
theorem automorphism_two_rank_le_ten : primeRank 2 (MulAut ParrottGroup) ≤ 10 := by
  have h := automorphism_primeRank_le_add_of_outer_card (p := 2) (n := 1)
    (RelativeSylowMarking.center_eq_bot parrottFiniteImageEquiv)
    (by simpa using SharpOuterBound.parrott_outer_card_le_two)
  have hr := parrott_two_rank_le_nine
  omega

/-- The improved rank bound is strictly below the Frobenius degree threshold. -/
theorem automorphism_two_rank_degree_gap :
    2 * (primeRank 2 (MulAut ParrottGroup) + 1) < 24 := by
  have h := automorphism_two_rank_le_ten
  omega

end Tits.AutomorphismTwoRank.FourthPower
