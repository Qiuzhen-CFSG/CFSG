module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootPointAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Points
public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

def rowEquiv (g : Ambient F) : Vector F ≃ₗ[F] Vector F where
  toFun v := v ᵥ* g.val
  invFun v := v ᵥ* (g⁻¹).val
  left_inv v := by dsimp only; rw [Matrix.vecMul_vecMul, ← Units.val_mul]; simp
  right_inv v := by dsimp only; rw [Matrix.vecMul_vecMul, ← Units.val_mul]; simp
  map_add' v w := Matrix.add_vecMul _ _ _
  map_smul' a v := Matrix.smul_vecMul _ _ _

def pointRight (g : Ambient F) : Projective F → Projective F :=
  Projectivization.map (rowEquiv g).toLinearMap (rowEquiv g).injective

theorem affineVector_root_mul (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (a b c d e f : F) :
    affineVector m a b c ᵥ* (rootElement m d e f).val =
      affineVector m (a+d) (b+e-a*(theta F m d)^3)
        (c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
  change (rootMatrix m a b c * rootMatrix m d e f) 0 = _
  rw [rootMatrix_mul m hcard]
  rfl

theorem infinityVector_root_mul (m : ℕ) (a b c : F) :
    (infinityVector : Vector F) ᵥ* (rootElement m a b c).val = infinityVector := by
  ext i
  fin_cases i <;>
    simp [infinityVector, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      rootMatrix_expanded, rootExpanded]

theorem pointRight_affine_root (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (a b c d e f : F) :
    pointRight (rootElement m d e f) (affinePoint m a b c) =
      affinePoint m (a+d) (b+e-a*(theta F m d)^3)
        (c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
  unfold pointRight affinePoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨1,?_⟩
  simpa only [one_smul, rowEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using (affineVector_root_mul m hcard a b c d e f).symm

theorem pointRight_infinity_root (m : ℕ) (a b c : F) :
    pointRight (rootElement m a b c) infinityPoint = infinityPoint := by
  unfold pointRight infinityPoint
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨1,?_⟩
  simpa only [one_smul, rowEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using (infinityVector_root_mul m a b c).symm

theorem root_preserves_pointSet (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
    (g : rootSubgroup m hcard) {p : Projective F} (hp : p ∈ pointSet m) :
    pointRight g.val p ∈ pointSet m := by
  obtain ⟨⟨d,e,f⟩,hg⟩ := g.property
  obtain ⟨p,rfl⟩ := hp
  cases p with
  | none =>
    change pointRight g.val infinityPoint ∈ pointSet m
    rw [← hg,pointRight_infinity_root]
    exact ⟨none,rfl⟩
  | some p =>
    obtain ⟨a,b,c⟩ := p
    change pointRight g.val (affinePoint m a b c) ∈ pointSet m
    rw [← hg,pointRight_affine_root m hcard]
    exact ⟨some (_,_,_),rfl⟩
end Atlas.ReeG2
