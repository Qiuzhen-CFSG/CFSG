module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus

/-!
# The original centralizer and normal-closure counts

The actual normalizer-growth producer and the independent TI/order-four census
prove GLS IV, Chapter 2, Lemma 15.6 from the source Context and the earlier
local two-core conclusions. In particular J=U has order two and its literal
normal closure in M is R₁=N_V(AU), of order 2q². The actual local model embedding
is constructed by the earlier freeness proof, not supplied as a certificate.

The original square census and M-conjugators are retained for Lemma 15.7.
No supplement M=VD or later complement census is used.
Source: refs/KGroup/GLS4/Chapter2.tex, lines 2718–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)

/-- Lemma 15.6 with normalizer growth, the original census, and the local
model embedding discharged; only the earlier two-core conclusions remain. -/
public theorem Context.centralizer_counts_of_localTwoData (hs : CentralizerLocalTwoData d) :
    Nat.card (centralizer (residualGenerated M z t : Set G)) = 2 ∧
      Nat.card (normalClosure
        ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M)) =
        2 * (2 ^ n) ^ 2 :=
  SourceCount.source_centralizer_counts d hs (SourceCount.normalizerData d hs)

namespace SourceCount
local notation "J" => centralizer (residualGenerated M z t : Set G)
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

public theorem centralizer_eq_twoCore (hs : CentralizerLocalTwoData d) : J = U := by
  obtain ⟨hm⟩ := d.centralizerLocalModelData
  exact centralizer_eq_twoCore_of_card_two d hm hs
    (twoCore_card_of_census d hs (source_coset_witness d hs (normalizerData d hs)))

/-- Identify the actual normal closure used in the subsequent source lemma. -/
public theorem normalClosure_centralizer_eq_sourceNormalizer
    (hs : CentralizerLocalTwoData d) :
    normalClosure ((J).subgroupOf M : Set M) = (R).subgroupOf M := by
  rw [centralizer_eq_twoCore d hs]
  exact normalClosure_twoCore_eq_sourceNormalizer d hs (normalizerData d hs)
    (twoCore_card_of_census d hs (source_coset_witness d hs (normalizerData d hs)))

/-- The original exact census and M-fusion, after proving |U|=2 and
without assuming a complement to D. -/
public theorem source_census (hs : CentralizerLocalTwoData d) :
    Nat.card {x : R // x ^ 2 = 1} = (2 ^ n) ^ 2 + 2 ^ n ∧
    Nat.card {x : R // orderOf x = 4} = 2 ^ n * (2 ^ n - 1) ∧
    ∀ x ∈ R, x ^ 2 = 1 → x ∉ A →
      ∃ m ∈ M, ∃ u ∈ J, u ≠ 1 ∧ MulAut.conj m u = x := by
  have hg := normalizerData d hs
  have hU := twoCore_card_of_census d hs (source_coset_witness d hs hg)
  refine ⟨?_, source_order_four_card d hs hg, ?_⟩
  · simpa only [hU, Nat.reduceSub, mul_one] using source_square_one_card d hs hg
  · intro x hx hx2 hxA
    rw [centralizer_eq_twoCore d hs]
    exact source_square_one_fusion d hs hg hx hx2 hxA

end SourceCount
end BenderSuzuki.ZD.LinearExclusion
