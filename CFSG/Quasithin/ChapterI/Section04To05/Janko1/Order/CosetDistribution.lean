module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Setup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.FixedPoints
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution

/-!
# From Bender's actual coset distribution to the counting parameters

The base fiber has seven involutions. The explicit distribution of the
non-base fibers gives their total and the number of occupied cosets.
Combining these with `120 |J| = 168 |G:H|` bounds `m`. The independent
order-five fixed-point congruence gives the divisibility in (4.6).
All subtractions use the distribution's explicit `e + 1 ≤ d` bound.

The final assembly constructs the normalizer data and the actual coset
distribution from `BenderPrimeData`, then applies the counting argument.
Thus `bender_countData` needs only the original centralizer data and the
earlier odd-prime local results. The order theorem's assembly owner must
still construct those odd-prime results from the source hypotheses.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, pp.226–227, especially (4.4)–(4.6).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- All unlisted positive-index coset counts vanish in the literal distribution. -/
public theorem BenderDistributionData.other_cosets_eq_zero
    {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G} {d : ℕ}
    (distribution : BenderDistributionData h d) (n : ℕ)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn3 : n ≠ 3) (hn6 : n ≠ 6) (hn7 : n ≠ 7) :
    benderCosetCount (normalizer (h.sylow : Set G)) n = 0 := by
  let H := normalizer (h.sylow : Set G)
  have : IsEmpty {ω : G ⧸ H // ω ≠ benderBaseCoset H ∧ Nat.card (BenderFiber H ω) = n} := by
    refine ⟨fun ω => ?_⟩
    have hs := distribution.fiber_sizes ω ω.2.1
    rw [ω.2.2] at hs
    rcases hs with hs | hs | hs | hs | hs
    · exact hn0 hs
    · exact hn1 hs
    · exact hn3 hs
    · exact hn6 hs
    · exact hn7 hs
  exact Nat.card_of_isEmpty

/-- Bender (4.4)–(4.6) follow from the actual coset distribution and the
normalizer theorem. The two group-theoretic premises remain explicit;
`localData.commuting_five` supplies the fixed-point congruence. -/
public theorem bender_countData_of_distribution
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
    (normalizerData : BenderNormalizerData h) (distribution : BenderDistributionData h d) :
    Nonempty (BenderCountData G d) := by
  obtain ⟨hi, hJ⟩ := bender_fiber_sums (normalizer (h.sylow : Set G)) distribution.fiber_sizes
  simp only [h.bender_base_fiber_card, distribution.single_cosets,
    distribution.centralized_singletons, distribution.triple_cosets,
    distribution.sextuple_cosets, distribution.septuple_cosets] at hi hJ
  have horder : (normalizer (h.sylow : Set G)).index * 168 =
      Nat.card {x : G // orderOf x = 2} * 120 := by
    rw [← normalizerData.normalizer_card, Subgroup.index_mul_card,
      h.card_eq_involution_count_mul]
  have hnonnegative := distribution.e_add_one_le_d
  have hcount : Nat.card {x : G // orderOf x = 2} =
      7 * (1 + 8 * (4 * d + 3 * distribution.m - 1)) := by omega
  have hm : distribution.m ≤ d + distribution.e + 1 := by omega
  have hcongruence : 5 ∣ 2 * d + 2 * distribution.m - 1 := by
    have hmod := h.bender_involutions_mod_five localData
    change Nat.card {x : G // orderOf x = 2} % 5 = d % 5 at hmod
    omega
  exact ⟨{
    e := distribution.e
    m := distribution.m
    e_le_one := distribution.e_le_one
    m_le := hm
    congruence := hcongruence
    involutions := hcount }⟩

/-- Bender's counting conclusions (4.4)–(4.6) from the original local
centralizer hypotheses and the earlier odd-prime results. The normalizer
theorem (4.3) and the literal coset distribution are constructed internally;
no normalizer, distribution, or ambient-order premise remains. -/
public theorem bender_countData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d) :
    Nonempty (BenderCountData G d) := by
  have normalizerData := h.bender_normalizerData localData
  obtain ⟨distribution⟩ := h.bender_distributionData d localData normalizerData
  exact h.bender_countData_of_distribution localData normalizerData distribution

end CFSG.Quasithin.Janko1CentralizerData
