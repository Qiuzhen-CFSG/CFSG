module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Model

/-!
# The actual pair of orthogonal summands

This predicate records the action on the two coordinate summands, including
the possibility of exchanging them. Every element of the concrete swapped
permutation model has this property. The converse recognition of form-preserving
maps is a separate geometric input; the predicate assumes no permutation model.

Source: the summand decomposition in Aschbacher–Smith, G.11.2(12), printed
p.364 of the combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace BinaryPermutation.TerminalOrthogonal.PairedBorel
open PairedFive

/-- A linear automorphism preserves the unordered pair of the two actual
coordinate summands. This records their action, without assuming a group model. -/
def PreservesSummandPair (f : Space ≃ₗ[ZMod 2] Space) : Prop :=
  ((∀ v : Factor, (f (v, 0)).2 = 0) ∧ (∀ v : Factor, (f (0, v)).1 = 0)) ∨
  ((∀ v : Factor, (f (v, 0)).1 = 0) ∧ (∀ v : Factor, (f (0, v)).2 = 0))

lemma modelAction_preservesSummandPair (g : Model) : PreservesSummandPair (modelAction g) := by
  by_cases hg : g.right = 1
  · left
    constructor <;> intro v <;> simp [modelAction_apply, hg]
  · right
    constructor <;> intro v <;> simp [modelAction_apply, hg]

end BinaryPermutation.TerminalOrthogonal.PairedBorel
