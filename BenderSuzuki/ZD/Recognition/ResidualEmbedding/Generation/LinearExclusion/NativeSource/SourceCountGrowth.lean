module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth.Squares

/-!
# The source normalizer-growth producer for Lemma 15.6

All four fields of the published intermediate interface now follow from the
original source Context and the earlier local two-core conclusions. The first
TI count and two coprime normalizer sections prove the order and normality of
R₁=N_V(AU); its quotient torus action and C_U(x)=1 prove the square condition.
These conclusions feed the independent involution/order-four census without
assuming the order of J, its normal closure, or a supplement for M.

Source: GLS IV, Chapter 2, Lemma 15.6, lines 2718–2730.
-/

namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup
universe u

/-- The original normalizer data, with every normalizer-growth premise discharged. -/
public theorem normalizerData
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {z t : G} {n : ℕ} (d : Context Z M z t n)
    (hs : CentralizerLocalTwoData d) : NormalizerData d where
  relative_normal := sourceNormalizer_relative_normal d hs
  card := sourceNormalizer_card d hs
  square_mem := fun _ hx => sourceNormalizer_square_mem_distinguished d hs hx
  torus_free := torus_free_section d hs (sourceNormalizer Z M z t)
    (closure (Z ∩ (M : Set G)) ⊔ twoCore M z t) inf_le_left
    (sup_le_sourceNormalizer d hs) inf_le_right le_sup_right
    (torus_normalizes_sourceNormalizer d hs) (torus_normalizes_sup d hs)

end BenderSuzuki.ZD.LinearExclusion.SourceCount
