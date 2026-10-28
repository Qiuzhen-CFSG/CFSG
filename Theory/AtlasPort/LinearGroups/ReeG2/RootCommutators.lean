module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootCommutators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
public import Mathlib.Algebra.Group.Commutator
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxHeartbeats 2000000

theorem root_gamma_central (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (a b c f : F) :
    rootElement m a b c * rootElement m 0 0 f =
      rootElement m 0 0 f * rootElement m a b c := by
  rw [rootElement_mul m hcard, rootElement_mul m hcard]
  simp [add_comm]

theorem root_alpha_beta_commutator (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (a b : F) :
    ⁅rootElement m a 0 0, rootElement m 0 b 0⁆ = rootElement m 0 0 (a*b) := by
  rw [commutatorElement_def, rootElement_inv m hcard, rootElement_inv m hcard]
  rw [rootElement_mul m hcard, rootElement_mul m hcard, rootElement_mul m hcard]
  simp only [map_zero, map_neg]
  congr 1 <;> ring_nf <;> reduce_mod_char!
end Atlas.ReeG2
