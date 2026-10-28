/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/TransitiveNoncommutative.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# TransitiveNoncommutative

A faithful transitive abelian action is regular.
Evaluation at a point is bijective, so unequal group order and degree imply noncommutativity.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/TransitiveNoncommutative.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- A faithful transitive commutative group has the same cardinality as its action set. -/
theorem card_eq_degree_of_commutative {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (a : X)
    (comm : ∀ g h : G, g * h = h * g) : Nat.card G = Nat.card X := by
  have hi : Function.Injective (fun g : G => g • a) := by
    intro g h he
    change g • a = h • a at he
    apply eq_of_smul_eq_smul (α := X)
    intro x
    obtain ⟨k,rfl⟩ := MulAction.exists_smul_eq G a x
    rw [← mul_smul, comm g k, mul_smul, he, ← mul_smul, comm k h, mul_smul]
  exact Nat.card_congr (Equiv.ofBijective _ ⟨hi,fun x => MulAction.exists_smul_eq G a x⟩)

theorem noncommuting_of_card_ne_degree {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] (a : X)
    (hne : Nat.card G ≠ Nat.card X) : ∃ g h : G, g * h ≠ h * g := by
  classical
  by_contra h
  push Not at h
  exact hne (card_eq_degree_of_commutative a h)

end Atlas.GroupTheory
