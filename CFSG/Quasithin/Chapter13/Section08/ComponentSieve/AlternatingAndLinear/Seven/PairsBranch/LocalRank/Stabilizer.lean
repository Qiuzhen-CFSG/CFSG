module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Partitions
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankZero

/-!
# Three-rank of the three-pairs stabilizer

The literal stabilizer of `{{0,1},{2,3},{4,5},{6}}` has order 48. The
finite count allows permutations of the three pairs. Since 3 divides 48
but 9 does not, its three-rank is exactly one. Later transport uses only
an embedding into this stabilizer, never surjectivity onto the symmetric
group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed p.959 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.LocalRank
open Equiv Subgroup

private instance (g : S7) : Decidable (g ∈ pairStabilizer) :=
  inferInstanceAs (Decidable
    (∀ i j, pairBlock (g i) = pairBlock (g j) ↔ pairBlock i = pairBlock j))

-- Use the direct permutation enumerator for this kernel-checked finite count.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- The partition stabilizer includes arbitrary permutation of the three pairs. -/
theorem pairStabilizer_card : Nat.card pairStabilizer = 48 := by
  let : Fintype S7 := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The full pair stabilizer has three-rank one. -/
theorem pairStabilizer_threeRank : primeRank 3 pairStabilizer = 1 := by
  have hu : primeRank 3 pairStabilizer ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le pairStabilizer).mpr
    intro E hE
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra! h
      have hdiv : 3 ^ 2 ∣ 48 := by
        rw [← pairStabilizer_card]
        exact (hn ▸ pow_dvd_pow 3 (by omega : 2 ≤ n)).trans E.card_subgroup_dvd_card
      norm_num at hdiv
    rw [hn]
    exact pow_le_pow_right' (by decide) hn1
  have hn : primeRank 3 pairStabilizer ≠ 0 := by
    intro hz
    have h := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    exact h (pairStabilizer_card ▸ (by decide : 3 ∣ 48))
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.LocalRank
