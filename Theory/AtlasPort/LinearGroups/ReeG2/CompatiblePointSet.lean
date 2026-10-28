module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/CompatiblePointSet.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.AffineCompatibility
public import Theory.AtlasPort.LinearGroups.ReeG2.CompatibilityCharts
public import Theory.AtlasPort.LinearGroups.ReeG2.CompatibilityScaling
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The bilinear equations recover precisely the already constructed projective chart. -/
theorem compatible_mk_mem_pointSet (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) {v w : Vector F}
    (hv : v ≠ 0) (h : pointCompatibility m v w) :
    Projectivization.mk F v hv ∈ pointSet m := by
  by_cases h0 : v 0 = 0
  · obtain ⟨h1,h2,h3,h4,h5⟩ := compatible_zero_first m h h0
    have h6 : v 6 ≠ 0 := by
      intro hh
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,hh]
    have he : Projectivization.mk F v hv = infinityPoint := by
      apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
      refine ⟨Units.mk0 (v 6) h6, ?_⟩
      ext i
      fin_cases i <;>
        simp [infinityVector, Units.smul_def, h0,h1,h2,h3,h4,h5,h6]
    exact ⟨none, he.symm⟩
  · let v' : Vector F := fun i => (v 0)⁻¹ * v i
    have hc := pointCompatibility_scale m h ((v 0)⁻¹) (inv_ne_zero h0)
    have hn : v' 0 = 1 := inv_mul_cancel₀ h0
    have hr := compatible_affine_reconstruction m hcard hc hn
    let a := sigma F m (v' 1)
    let b := -sigma F m (v' 2)
    let c := sigma F m (-(v' 1 * v' 2) - v' 3)
    have he : Projectivization.mk F v hv = affinePoint m a b c := by
      apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
      refine ⟨Units.mk0 (v 0) h0, ?_⟩
      ext i
      have hi := congrFun hr i
      change (v 0)⁻¹ * v i = affineVector m a b c i at hi
      simp only [Units.smul_def, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [← hi]
      field_simp
    exact ⟨some (a,b,c), he.symm⟩

end Atlas.ReeG2
