module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Reduction

/-!
# Conditional assembly of the proper linear centralizer count

The earlier local model and two-core inputs, the original normalizer geometry,
and the order-four coset census imply both cardinalities of GLS IV, Chapter 2,
Lemma 15.6. The normalizer and census premises remain explicit here. In
particular the formula concerns the literal normal closure inside M, as proved
by `SourceCount.normalClosure_twoCore_eq_sourceNormalizer`.

Source: refs/KGroup/GLS4/Chapter2.tex, Lemma 15.6, lines 2718–2745.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup
universe u

/-- The normalizer/census reduction for the original conditional Lemma 15.6.
Its final assembly must construct both remaining intermediate premises. -/
public theorem proper_linear_centralizer_counts_of_normalizer_and_census
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {z t : G} {n : ℕ} (d : Context Z M z t n)
    (hm : CentralizerLocalModelData d) (hs : CentralizerLocalTwoData d)
    (hg : SourceCount.NormalizerData d)
    (hc : ∃ x ∈ SourceCount.sourceNormalizer Z M z t, x ^ 2 ≠ 1 ∧
      ∀ u ∈ SourceCount.twoCore M z t, u ≠ 1 → (u * x) ^ 2 = 1) :
    Nat.card (centralizer (residualGenerated M z t : Set G)) = 2 ∧
      Nat.card (normalClosure
        ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M)) =
        2 * (2 ^ n) ^ 2 :=
  SourceCount.counts_of_normalizer_and_census d hm hs hg hc

end BenderSuzuki.ZD.LinearExclusion
