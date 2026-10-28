module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo.Refinement
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Mathlib.GroupTheory.PGroup

/-!
# The full normalizer of the second Held four-group is a two-group

Its elements preserve the Held graph and, by the fixed-set refinement, the
existing representative coloring. Held is perfect, so their permutations
are even. The even colored graph group has order at most 1024 and contains
the already certified representative of order at least 1024; hence its order
is exactly 2¹⁰. The faithful representation therefore embeds the full row
normalizer into a two-group. No order or simplicity certificate for Held,
nor any enumeration of normal elementary subgroups, is assumed.

Sources: Aschbacher–Smith 15.3.43, printed p.1140; GLS3 Table 5.3p;
the literal ATLAS degree-2058 graph and representative certificates.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers
open Subgroup LocalPairs.SylowGeometry.Calculations InnerNormalizer

private def representativeToColored : representative →* evenColoredGraphGroup where
  toFun g := ⟨representation g.val, normalizer_mem_evenColoredGraphGroup
    orbitSizeLabel_eq_card_orbit g.val (le_normalizer g.property)⟩
  map_one' := Subtype.ext (map_one representation)
  map_mul' g h := Subtype.ext (map_mul representation g.val h.val)

private theorem representativeToColored_injective : Function.Injective representativeToColored := by
  intro g h he
  have hv : representation g.val = representation h.val :=
    congrArg (fun z : evenColoredGraphGroup => z.val) he
  exact Subtype.ext (representation_injective hv)

private theorem colored_isPGroup : IsPGroup 2 evenColoredGraphGroup := by
  apply IsPGroup.of_card (n := 10)
  have hl := (representative_card_ge_of_orbit_labels orbitSizeLabel_eq_card_orbit).trans
    (Nat.card_le_card_of_injective representativeToColored representativeToColored_injective)
  exact le_antisymm evenColoredGraphGroup_card_le hl

set_option maxRecDepth 4096 in
private theorem normalizer_mem_colored (g : He)
    (hg : g ∈ normalizer (ambient 2 : Set He)) : representation g ∈ evenColoredGraphGroup := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  · exact RowTwo.normalizer_preserves_coloring g hg
  · exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g

private def normalizerToColored : normalizer (ambient 2 : Set He) →* evenColoredGraphGroup where
  toFun g := ⟨representation g.val, normalizer_mem_colored g.val g.property⟩
  map_one' := Subtype.ext (map_one representation)
  map_mul' g h := Subtype.ext (map_mul representation g.val h.val)

private theorem normalizerToColored_injective : Function.Injective normalizerToColored := by
  intro g h he
  have hv : representation g.val = representation h.val :=
    congrArg (fun z : evenColoredGraphGroup => z.val) he
  exact Subtype.ext (representation_injective hv)

/-- This bounds the full normalizer inside the actual Held carrier. -/
public theorem isPGroup_normalizer_two : IsPGroup 2 (normalizer (ambient 2 : Set He)) :=
  colored_isPGroup.of_injective normalizerToColored normalizerToColored_injective

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers
