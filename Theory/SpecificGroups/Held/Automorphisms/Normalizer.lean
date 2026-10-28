module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.LowerBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation
public import Mathlib.GroupTheory.Index

/-!
# Bounding the full Held permutation-normalizer quotient

The concrete orbit trees in `LowerBound` prove that Held has at least
4030387200 elements. `OrbitalPreservation` proves that its full permutation
normalizer preserves the finite relation in `GraphData`, and `GraphCardBound`
bounds the full preserving group by twice that many elements. Consequently
the relative normalizer quotient has order at most two and is a two-group.

The conditional graph reductions remain available. The final theorems
discharge both premises, without simplicity, perfectness or an exact Held
order calculation. The denominator is Held's copy inside its full normalizer.

Source: GLS3, Table 5.3p, and the fixed ATLAS `HeG1-p2058B0` permutations.
This is the normalizer-bound part of the outer-group calculation; realization
of abstract automorphisms is independent of this argument.
-/

namespace Held

/-- A graph containing the full normalizer and the explicit Held lower bound
give a bound on the order of the relative normalizer quotient. Both graph
premises must be discharged to complete the concrete calculation. -/
public theorem permutationNormalizerQuotient_card_le_two_of_graph
    (hn : Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) ≤
      NormalizerGraph.preservingGroup)
    (hc : Nat.card NormalizerGraph.preservingGroup ≤ 8060774400) :
    Nat.card PermutationNormalizerQuotient ≤ 2 := by
  let N := Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058)))
  let H := permutationGroup.subgroupOf N
  have hN : Nat.card N ≤ 8060774400 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hn)
      (Subgroup.inclusion_injective hn)).trans hc
  have hH : Nat.card H = Nat.card He :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      permutationGroup.le_normalizer).toEquiv
  have hmul := H.card_mul_index
  change Nat.card H * Nat.card PermutationNormalizerQuotient = Nat.card N at hmul
  rw [hH] at hmul
  have hlow := NormalizerBounds.card_lower_bound
  by_contra h
  have hm : 4030387200 * 3 ≤
      Nat.card He * Nat.card PermutationNormalizerQuotient :=
    Nat.mul_le_mul hlow (by omega)
  omega

/-- Conditional assembly of the desired two-group bound from the two finite
graph calculations. It uses no exact Held order or simplicity theorem. -/
public theorem isPGroup_permutationNormalizerQuotient_of_graph
    (hn : Subgroup.normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) ≤
      NormalizerGraph.preservingGroup)
    (hc : Nat.card NormalizerGraph.preservingGroup ≤ 8060774400) :
    IsPGroup 2 PermutationNormalizerQuotient := by
  have hQ := permutationNormalizerQuotient_card_le_two_of_graph hn hc
  have hpos : 0 < Nat.card PermutationNormalizerQuotient := Nat.card_pos
  apply IsPGroup.of_card_dvd_pow (n := 1)
  have hc' : Nat.card PermutationNormalizerQuotient = 1 ∨
      Nat.card PermutationNormalizerQuotient = 2 := by omega
  rcases hc' with h | h <;> simp [h]

/-- The quotient of the full degree-2058 permutation normalizer by its Held
subgroup has order at most two. -/
public theorem permutationNormalizerQuotient_card_le_two :
    Nat.card PermutationNormalizerQuotient ≤ 2 :=
  permutationNormalizerQuotient_card_le_two_of_graph
    NormalizerGraph.Orbital.normalizer_le_preservingGroup
    NormalizerGraph.card_preservingGroup_le

/-- The full permutation-normalizer quotient of the fixed Held model is a
two-group, with both finite graph premises discharged. -/
public theorem isPGroup_permutationNormalizerQuotient :
    IsPGroup 2 PermutationNormalizerQuotient :=
  isPGroup_permutationNormalizerQuotient_of_graph
    NormalizerGraph.Orbital.normalizer_le_preservingGroup
    NormalizerGraph.card_preservingGroup_le

end Held
