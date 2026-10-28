module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Invariants for recognizing a subgroup of Aut(UT₃(F₄))

The source normalizer acts on the root group with kernel its four-element
center. Its image therefore has order 288 and contains the inner automorphisms.
The full action on the center and a central cubic element modulo inner
automorphisms distinguish the graph–field action from other semilinear actions.

This file specifies those intrinsic invariants. It does not assert their
sufficiency or construct them for an ambient group. The subgroup-conjugacy
theorem and the source construction are separate obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(5–6), 46.3(2),
and 46.14, printed pp.29–30, 251, and 257–258.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Matrix.PSL3Four.RootNormalizerModel

/-- Conditions on the actual automorphism subgroup, retaining its action on
the center and a nontrivial central cubic coset modulo inner automorphisms. -/
structure AutomizerInvariants (H : Subgroup (MulAut Root)) : Prop where
  inner_le : (MulAut.conj : Root →* MulAut Root).range ≤ H
  card : Nat.card H = 288
  full_center_action : ∀ b : MulAut (center Root),
    ∃ h ∈ H, ∀ z : center Root, h z = (b z : Root)
  central_cubic : ∃ c ∈ H,
    c ∉ (MulAut.conj : Root →* MulAut Root).range ∧
    c ^ 3 ∈ (MulAut.conj : Root →* MulAut Root).range ∧
    ∀ h ∈ H, ⁅c, h⁆ ∈ (MulAut.conj : Root →* MulAut Root).range

end Matrix.PSL3Four.RootNormalizerModel
