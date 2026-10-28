module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/TorusCommutators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.TorusRootAction
public import Theory.AtlasPort.LinearGroups.ReeG2.RootCommutators
public import Theory.AtlasPort.FieldTheory.ReeScalarSquares
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

def betaCharacter (m : ℕ) (l : Fˣ) : F := (l : F) / (theta F m (l : F))^3

theorem exists_betaCharacter_ne_one (m : ℕ) (hp : Parameters F m) :
    ∃ l : Fˣ, betaCharacter m l ≠ 1 := by
  have hq : 3 < Nat.card F := lt_of_lt_of_le (by norm_num) (card_ge_27 hp)
  obtain ⟨a,ha,hsq⟩ := exists_scalar_square_ne_one hq
  refine ⟨Units.mk0 a ha,?_⟩
  intro h
  change a / (theta F m a)^3 = 1 at h
  have ht : (theta F m a)^3 ≠ 0 := pow_ne_zero _ ((map_ne_zero (theta F m)).2 ha)
  have he : a = (theta F m a)^3 := (div_eq_one_iff_eq ht).mp h
  have hs : sigma F m a = a := (sigma_eq_theta_cube a).trans he.symm
  have hc : a^3 = a := by rw [← sigma_square hp.cardinality, hs, hs]
  apply hsq
  apply mul_right_cancel₀ ha
  simpa [pow_succ] using hc

theorem torus_beta_commutator (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) (b : F) :
    ⁅(torus m l)⁻¹, rootElement m 0 b 0⁆ =
      rootElement m 0 ((betaCharacter m l - 1)*b) 0 := by
  rw [commutatorElement_def, inv_inv, torus_conjugate_root m hcard,
    rootElement_inv m hcard, rootElement_mul m hcard]
  simp [betaCharacter]
  congr 1
  ring

theorem torus_gamma_commutator (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) (c : F) :
    ⁅(torus m l)⁻¹, rootElement m 0 0 c⁆ =
      rootElement m 0 0 (((l : F)⁻¹ - 1)*c) := by
  rw [commutatorElement_def, inv_inv, torus_conjugate_root m hcard,
    rootElement_inv m hcard, rootElement_mul m hcard]
  simp
  congr 1
  ring
end Atlas.ReeG2
