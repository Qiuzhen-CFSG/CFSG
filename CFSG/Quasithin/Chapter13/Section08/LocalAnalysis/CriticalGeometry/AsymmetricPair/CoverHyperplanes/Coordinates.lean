module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Coordinate tests in the five-dimensional S₆ cover

The pair vectors lie in the augmentation core. Testing their displacements
recognizes a transposition, and testing the pairs on the other four letters
recognizes the stabilizer modulo the transposition's center. The finite tests
below are reduced by the Lean kernel, without native evaluation.

Source: Aschbacher–Smith, 13.8.7, printed p.949, last two paragraphs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes
open BinaryPermutation

abbrev Six := Fin 6
abbrev Perm := Equiv.Perm Six
abbrev Core := core Six
abbrev act := coreRepresentation Six

/-- The weight-two vector, with the coincident-letter case equal to zero. -/
def pair (i j : Six) : Full Six := Pi.single i 1 + Pi.single j 1

/-- The actual pair vector in the augmentation core. -/
def pairCore (i j : Six) : Core := ⟨pair i j, by
  simp [pair, mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private def delta (g : Perm) (i : Six) : Full Six :=
  representation Six g (pair 0 i) - pair 0 i

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8192 in
/-- Pair displacements contained in a binary line recognize a transposition. -/
theorem pair_displacement_test : ∀ g : Perm,
    (∀ i j, (act g (pairCore 0 i) - pairCore 0 i : Core) = 0 ∨
      (act g (pairCore 0 j) - pairCore 0 j : Core) = 0 ∨
      act g (pairCore 0 i) - pairCore 0 i = act g (pairCore 0 j) - pairCore 0 j) →
    g = 1 ∨ ∃ i j, i ≠ j ∧ g = Equiv.swap i j := by
  have cert : ∀ g : Perm,
      (∀ i j, delta g i = 0 ∨ delta g j = 0 ∨ delta g i = delta g j) →
        g = 1 ∨ ∃ i j, i ≠ j ∧ g = Equiv.swap i j := by decide +kernel
  intro g h
  apply cert g
  intro i j
  rcases h i j with hi | hj | he
  · exact Or.inl (congrArg Subtype.val hi)
  · exact Or.inr (Or.inl (congrArg Subtype.val hj))
  · exact Or.inr (Or.inr (congrArg Subtype.val he))

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8192 in
/-- On the standard transposition axis, displacement into its center forces
identity or that transposition. Only pair vectors on the other four letters
are needed for this test. -/
theorem axis_pair_test : ∀ g : Perm,
    (∀ k l : Six, k ≠ 0 → k ≠ 1 → l ≠ 0 → l ≠ 1 →
      act g (pairCore k l) - pairCore k l = 0 ∨
      act g (pairCore k l) - pairCore k l = pairCore 0 1) →
    g = 1 ∨ g = Equiv.swap 0 1 := by
  have cert : ∀ g : Perm,
      (∀ k l : Six, k ≠ 0 → k ≠ 1 → l ≠ 0 → l ≠ 1 →
        representation Six g (pair k l) - pair k l = 0 ∨
        representation Six g (pair k l) - pair k l = pair 0 1) →
      g = 1 ∨ g = Equiv.swap 0 1 := by decide +kernel
  intro g h
  apply cert g
  intro k l hk0 hk1 hl0 hl1
  rcases h k l hk0 hk1 hl0 hl1 with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverHyperplanes
end
