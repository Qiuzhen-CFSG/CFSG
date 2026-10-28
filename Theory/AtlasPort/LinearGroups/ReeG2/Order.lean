module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/Order.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.ExactStabilizer
public import Mathlib.GroupTheory.Index
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The distinguished point as an element of the actual invariant point set. -/
def infinity (m : ℕ) : pointSet (F := F) m := ⟨infinityPoint,⟨none,rfl⟩⟩

theorem infinityStabilizer_eq_borel (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    letI := pointAction m hcard
    MulAction.stabilizer (Model F m) (infinity (F := F) m) =
      (borel m hcard).subgroupOf (generated F m) := by
  letI := pointAction m hcard
  ext g
  change g • infinity (F := F) m = infinity (F := F) m ↔ g.val ∈ borel m hcard
  rw [Subtype.ext_iff]
  change pointRight g.val⁻¹ infinityPoint = infinityPoint ↔ g.val ∈ borel m hcard
  rw [fixes_infinity_iff_mem_borel m hcard _ ((generated F m).inv_mem g.property),
    Subgroup.inv_mem_iff]

/-- Uniform order of the actual seven-dimensional generated matrix group. -/
theorem order (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    Nat.card (Model F m) = Nat.card F ^ 3 * (Nat.card F ^ 3 + 1) * (Nat.card F - 1) := by
  letI := pointAction m hcard
  letI : MulAction.IsPretransitive (Model F m) (pointSet (F := F) m) :=
    (pointAction_preprimitive m hcard).toIsPretransitive
  have hs : Nat.card (MulAction.stabilizer (Model F m) (infinity (F := F) m)) =
      Nat.card (borel m hcard) := by
    rw [infinityStabilizer_eq_borel m hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (borel_le_generated m hcard)).toEquiv
  calc
    Nat.card (Model F m) = Nat.card (MulAction.stabilizer (Model F m) (infinity (F := F) m)) *
        (MulAction.stabilizer (Model F m) (infinity (F := F) m)).index :=
      (Subgroup.card_mul_index _).symm
    _ = Nat.card (borel m hcard) * Nat.card (pointSet (F := F) m) := by
      rw [hs,MulAction.index_stabilizer_of_transitive]
    _ = _ := by rw [card_borel,card_pointSet]; ring

end Atlas.ReeG2
