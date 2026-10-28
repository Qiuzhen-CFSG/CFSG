module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/TorusPointAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.ProjectiveAction
public import Theory.AtlasPort.LinearGroups.ReeG2.TorusRootAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxHeartbeats 2000000

theorem pointRight_zero_torus (m : ℕ) (l : Fˣ) :
    pointRight (torus m l) (affinePoint m 0 0 0) = affinePoint m 0 0 0 := by
  unfold pointRight affinePoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.map (theta F m).toMonoidHom l,?_⟩
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, affineVector, rootMatrix_zero, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Units.smul_def]

theorem pointRight_infinity_torus (m : ℕ) (l : Fˣ) :
    pointRight (torus m l) infinityPoint = infinityPoint := by
  unfold pointRight infinityPoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨(Units.map (theta F m).toMonoidHom l)⁻¹,?_⟩
  ext i
  fin_cases i <;>
    simp [rowEquiv_apply, infinityVector, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Units.smul_def]

theorem pointRight_affine_torus (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) (a b c : F) :
    pointRight (torus m l) (affinePoint m a b c) =
      affinePoint m (a * (theta F m (l : F))^3 / (l : F)^2)
        (b * (l : F) / (theta F m (l : F))^3) (c / (l : F)) := by
  have ht := torus_conjugate_root m hcard l a b c
  have he : rootElement m a b c * torus m l = torus m l *
      rootElement m (a * (theta F m (l : F))^3 / (l : F)^2)
        (b * (l : F) / (theta F m (l : F))^3) (c / (l : F)) := by
    rw [← ht]
    group
  rw [← pointRight_zero_root m hcard a b c]
  change (pointRight (torus m l) ∘ pointRight (rootElement m a b c)) _ = _
  rw [← pointRight_mul,he,pointRight_mul]
  change pointRight _ (pointRight (torus m l) (affinePoint m 0 0 0)) = _
  rw [pointRight_zero_torus,pointRight_zero_root m hcard]

theorem torus_preserves_pointSet (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (l : Fˣ) {p : Projective F} (hp : p ∈ pointSet m) :
    pointRight (torus m l) p ∈ pointSet m := by
  obtain ⟨p,rfl⟩ := hp
  cases p with
  | none =>
    change pointRight (torus m l) infinityPoint ∈ pointSet m
    rw [pointRight_infinity_torus]
    exact ⟨none,rfl⟩
  | some p =>
    obtain ⟨a,b,c⟩ := p
    change pointRight (torus m l) (affinePoint m a b c) ∈ pointSet m
    rw [pointRight_affine_torus m hcard]
    exact ⟨some (_,_,_),rfl⟩
end Atlas.ReeG2
