module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.GraphBound.Certificate

/-!
# The full automorphism bound for the 693-vector sum graph

Individualizing vertices 0, 73, 33, 10, 143, 1 gives successive orbit bounds
693, 2, 30, 4, 8, 2. The certificate checks invariant colorings for these
stabilizers and proves that the last coloring is injective. Orbit–stabilizer
therefore bounds the full group of permutations preserving `Adj` by 2661120.
By `Geometry.adj_iff`, this is precisely the graph whose adjacency means that
the sum of the two listed binary vectors is listed again.

The untrusted trace and its construction are in `ImageBound/source/refinement.json`
and `refine.py`; provenance and ATLAS attribution are in the adjacent `README.md`.
This graph bound has no coordinate-identification or color-preservation premises.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry

open GraphBoundCertificate

/-- The full permutation group preserving the 693-vector sum relation has
order at most 2661120. -/
theorem preservingGroup_card_le : Nat.card preservingGroup ≤ 2661120 :=
  Refinement.preservingGroup_card_le_of_colors
    stage1Color stage2Color stage3Color stage4Color stage5Color stage6Color
    stage1_preserves stage2_preserves stage3_preserves
    stage4_preserves stage5_preserves stage6_preserves
    stage1_size stage2_size stage3_size stage4_size stage5_size stage6_injective

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry
