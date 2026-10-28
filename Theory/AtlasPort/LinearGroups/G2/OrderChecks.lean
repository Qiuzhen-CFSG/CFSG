module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/OrderChecks.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Order
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.NormNum

/-!
Specializing the uniform orbit–stabilizer formulas gives exact group and
singular-point counts for small finite fields.
-/

@[expose] public section

namespace Atlas.G2.OrderChecks

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem binary_order : Nat.card (Model (ZMod 2)) = 12096 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_order : Nat.card (Model (ZMod 3)) = 4245696 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem four_order : Nat.card (Model (GaloisField 2 2)) = 251596800 := by
  rw [card_Model, GaloisField.card 2 2 (by decide)]
  norm_num

theorem five_order : Nat.card (Model (ZMod 5)) = 5859000000 := by
  rw [card_Model]
  norm_num [Nat.card_eq_fintype_card]

theorem eight_order : Nat.card (Model (GaloisField 2 3)) = 4329310519296 := by
  rw [card_Model, GaloisField.card 2 3 (by decide)]
  norm_num

theorem binary_points : Nat.card (SingularPoints (ZMod 2)) = 63 := by
  rw [card_singularPoints]
  norm_num [Nat.card_eq_fintype_card]

theorem ternary_points : Nat.card (SingularPoints (ZMod 3)) = 364 := by
  rw [card_singularPoints]
  norm_num [Nat.card_eq_fintype_card]

theorem four_points : Nat.card (SingularPoints (GaloisField 2 2)) = 1365 := by
  rw [card_singularPoints, GaloisField.card 2 2 (by decide)]
  norm_num

end Atlas.G2.OrderChecks
