/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24ConstructionPackage
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
# Mathieu23PointStabilizer

The stabilizer of a Golay coordinate acts faithfully and four-transitively on the other
twenty-three coordinates. Restricting the ambient five-transitive action constructs this
model, and orbit-stabilizer gives its order 10200960.

Source: `Atlas/Mathieu/Mathieu23PointStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

/-! The actual point stabilizer acting on the other 23 Golay coordinates. -/

namespace Atlas.Codes

abbrev Mathieu23PointModel (a : Omega) := MulAction.stabilizer Mathieu24CodeModel a
abbrev Mathieu23Points (a : Omega) := SubMulAction.ofStabilizer Mathieu24CodeModel a

def mathieu23_embedding (a : Omega) : Mathieu23PointModel a →* Mathieu24CodeModel :=
  (MulAction.stabilizer Mathieu24CodeModel a).subtype

theorem mathieu23_embedding_injective (a : Omega) :
    Function.Injective (mathieu23_embedding a) := Subtype.val_injective

theorem mathieu23_degree (a : Omega) : Nat.card (Mathieu23Points a) = 23 := by
  have h := SubMulAction.nat_card_ofStabilizer_add_one_eq Mathieu24CodeModel a
  have hc : Nat.card Omega = 24 := by simp [Omega, HexIndex]
  rw [hc] at h
  change Nat.card (Mathieu23Points a) + 1 = 24 at h
  omega

theorem mathieu23_faithful (a : Omega) :
    FaithfulSMul (Mathieu23PointModel a) (Mathieu23Points a) :=
  Atlas.GroupTheory.stabilizer_complement_faithful a

theorem mathieu23_four_transitive (a : Omega) :
    MulAction.IsMultiplyPretransitive (Mathieu23PointModel a) (Mathieu23Points a) 4 := by
  have := mathieu24_five_transitive
  have : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega, HexIndex])
  have : MulAction.IsPretransitive Mathieu24CodeModel Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive (G := Mathieu24CodeModel)
      (α := Omega)
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := a)).mp
    mathieu24_five_transitive

theorem mathieu23_order (a : Omega) : Nat.card (Mathieu23PointModel a) = 10200960 := by
  let e : Fin 1 ↪ Omega := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  have he : Set.range e = {a} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩; exact hi.symm
    · intro hx; exact ⟨0, hx.symm⟩
  have hs : orderedPointStabilizer e = MulAction.stabilizer Mathieu24CodeModel a := by
    unfold orderedPointStabilizer
    rw [he]
    ext g
    simp [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  change Nat.card (MulAction.stabilizer Mathieu24CodeModel a) = 10200960
  rw [← hs]
  exact mathieu24_one_point_order e

end Atlas.Codes
