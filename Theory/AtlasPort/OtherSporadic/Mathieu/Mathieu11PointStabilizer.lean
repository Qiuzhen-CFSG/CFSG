/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadPointOrders
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Theory.AtlasPort.OtherSporadic.GroupTheory.TransitiveNoncommutative

/-!
# Mathieu11PointStabilizer

Fixing an interior point in the dodecad model gives the concrete degree-eleven Mathieu
action. Restriction transfers faithfulness and four-transitivity, while orbit-stabilizer
gives order 7920 and excludes commutativity.

Source: `Atlas/Mathieu/Mathieu11PointStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev Mathieu11PointModel (D : Dodecad) (a : Mathieu12Points D) :=
  MulAction.stabilizer (Mathieu12DodecadModel D) a
abbrev Mathieu11Points (D : Dodecad) (a : Mathieu12Points D) :=
  SubMulAction.ofStabilizer (Mathieu12DodecadModel D) a

def mathieu11_embedding (D : Dodecad) (a : Mathieu12Points D) :
    Mathieu11PointModel D a →* Mathieu12DodecadModel D :=
  (Mathieu11PointModel D a).subtype

theorem mathieu11_embedding_injective (D : Dodecad) (a : Mathieu12Points D) :
    Function.Injective (mathieu11_embedding D a) := Subtype.val_injective

theorem mathieu11_degree (D : Dodecad) (a : Mathieu12Points D) : Nat.card (Mathieu11Points D a) = 11 := by
  have h := SubMulAction.nat_card_ofStabilizer_add_one_eq (Mathieu12DodecadModel D) a
  rw [mathieu12_degree] at h
  change Nat.card (Mathieu11Points D a) + 1 = 12 at h
  omega

theorem mathieu11_faithful (D : Dodecad) (a : Mathieu12Points D) :
    FaithfulSMul (Mathieu11PointModel D a) (Mathieu11Points D a) := by
  have := mathieu12_faithful D
  exact Atlas.GroupTheory.stabilizer_complement_faithful a

theorem mathieu11_four_transitive (D : Dodecad) (a : Mathieu12Points D) :
    MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) 4 := by
  have := mathieu12_five_transitive D
  have : MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by rw [mathieu12_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu12DodecadModel D) (Mathieu12Points D) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := a)).mp
    (mathieu12_five_transitive D)

theorem mathieu11_order (D : Dodecad) (a : Mathieu12Points D) : Nat.card (Mathieu11PointModel D a) = 7920 := by
  let e : Fin 1 ↪ Mathieu12Points D := ⟨fun _ => a,fun _ _ _ => Subsingleton.elim _ _⟩
  have he : Set.range e = {a} := by
    ext x
    simp only [Set.mem_range,Set.mem_singleton_iff]
    exact ⟨fun ⟨_,h⟩ => h.symm,fun h => ⟨0,h.symm⟩⟩
  have hs : dodecadOrderedStabilizer D e = Mathieu11PointModel D a := by
    unfold dodecadOrderedStabilizer
    rw [he]
    ext g
    simp [mem_fixingSubgroup_iff,MulAction.mem_stabilizer_iff]
  rw [← hs]
  exact mathieu12_one_point_order D e

theorem mathieu11_order_factorization (D : Dodecad) (a : Mathieu12Points D) :
    Nat.card (Mathieu11PointModel D a) = 2^4 * 3^2 * 5 * 11 := by
  rw [mathieu11_order]
  rfl

theorem mathieu11_noncommuting_pair (D : Dodecad) (a : Mathieu12Points D) :
    ∃ g h : Mathieu11PointModel D a, g*h ≠ h*g := by
  have := mathieu11_faithful D a
  have := mathieu11_four_transitive D a
  have : MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4)
      (by rw [mathieu11_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hcard : 0 < Nat.card (Mathieu11Points D a) := by rw [mathieu11_degree]; decide
  have hn : Nonempty (Mathieu11Points D a) := (Nat.card_pos_iff.mp hcard).1
  let x : Mathieu11Points D a := Classical.choice hn
  apply Atlas.GroupTheory.noncommuting_of_card_ne_degree (G := Mathieu11PointModel D a) x
  rw [mathieu11_order,mathieu11_degree]
  decide

end Atlas.Codes
