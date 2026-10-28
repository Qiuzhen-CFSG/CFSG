/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22PointStabilizer

/-!
# Mathieu21PointStabilizer

The stabilizer of three distinct Golay coordinates acts faithfully and doubly
transitively on the remaining twenty-one coordinates. Restriction of the preceding
Mathieu action and orbit-stabilizer give its embedding, order, and noncommutativity.

Source: `Atlas/Mathieu/Mathieu21PointStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Atlas.Codes

abbrev Mathieu21PointModel (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :=
  MulAction.stabilizer (Mathieu22PointModel a b) c
abbrev Mathieu21Points (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :=
  SubMulAction.ofStabilizer (Mathieu22PointModel a b) c

instance mathieu21MulAction (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    MulAction (Mathieu21PointModel a b c) (Mathieu21Points a b c) :=
  SubMulAction.mulAction _

def mathieu21_embedding (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    Mathieu21PointModel a b c →* Mathieu24CodeModel :=
  (mathieu22_embedding a b).comp (Mathieu21PointModel a b c).subtype

theorem mathieu21_embedding_injective (a : Omega) (b : Mathieu23Points a)
    (c : Mathieu22Points a b) : Function.Injective (mathieu21_embedding a b c) :=
  (mathieu22_embedding_injective a b).comp Subtype.val_injective

theorem mathieu21_degree (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    Nat.card (Mathieu21Points a b c) = 21 := by
  have h := SubMulAction.nat_card_ofStabilizer_add_one_eq (Mathieu22PointModel a b) c
  rw [mathieu22_degree] at h
  change Nat.card (Mathieu21Points a b c) + 1 = 22 at h
  omega

theorem mathieu21_faithful (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    FaithfulSMul (Mathieu21PointModel a b c) (Mathieu21Points a b c) := by
  have := mathieu22_faithful a b
  exact Atlas.GroupTheory.stabilizer_complement_faithful c

theorem mathieu22_pretransitive (a : Omega) (b : Mathieu23Points a) :
    MulAction.IsPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) := by
  have := mathieu22_three_transitive a b
  have : MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3) (by rw [mathieu22_degree]; decide)
  exact MulAction.isPretransitive_of_is_two_pretransitive (G := Mathieu22PointModel a b)
    (α := Mathieu22Points a b)

theorem mathieu21_two_transitive (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    MulAction.IsMultiplyPretransitive (Mathieu21PointModel a b c) (Mathieu21Points a b c) 2 := by
  have := mathieu22_pretransitive a b
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := c)).mp
    (mathieu22_three_transitive a b)

theorem mathieu21_order (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    Nat.card (Mathieu21PointModel a b c) = 20160 := by
  let e : Fin 1 ↪ Mathieu22Points a b := ⟨fun _ => c,fun _ _ _ => Subsingleton.elim _ _⟩
  have he : Set.range e = {c} := by
    ext x
    simp only [Set.mem_range,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,hi⟩; exact hi.symm
    · intro hx; exact ⟨0,hx.symm⟩
  have hs : mathieu22TupleStabilizer a b e = Mathieu21PointModel a b c := by
    unfold mathieu22TupleStabilizer
    rw [he]
    ext g
    simp [mem_fixingSubgroup_iff,MulAction.mem_stabilizer_iff]
  rw [← hs]
  exact mathieu22_one_point_order a b e

theorem mathieu21_noncommuting_pair (a : Omega) (b : Mathieu23Points a)
    (c : Mathieu22Points a b) : ∃ g h : Mathieu21PointModel a b c, g*h ≠ h*g := by
  have := mathieu21_faithful a b c
  have := mathieu21_two_transitive a b c
  have : MulAction.IsPretransitive (Mathieu21PointModel a b c) (Mathieu21Points a b c) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (Mathieu21Points a b c) by
    rw [mathieu21_degree]; decide)).1
  apply Atlas.GroupTheory.noncommuting_of_card_ne_degree (G := Mathieu21PointModel a b c) x
  rw [mathieu21_order,mathieu21_degree]
  decide

end Atlas.Codes
