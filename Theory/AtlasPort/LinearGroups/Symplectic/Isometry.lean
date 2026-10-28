import Theory.AtlasPort.LinearGroups.Symplectic.Basic
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
set_option warningAsError false

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- The faithful linear representation of the primary matrix group. -/
def toLinear : Sp n F →* (Vector n F ≃ₗ[F] Vector n F) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Vector n F)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp toGL)

@[simp] theorem toLinear_apply (g : Sp n F) (x : Vector n F) : toLinear g x = g • x := rfl

/-- Recover the primary matrix element from an actual form-preserving linear map. -/
def ofLinear (g : Vector n F ≃ₗ[F] Vector n F)
    (hg : ∀ x y, form (g x) (g y) = form x y) : Sp n F :=
  ⟨LinearMap.toMatrix' g.toLinearMap, mem_iff_preserves.mpr (by
    intro x y
    simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using hg x y)⟩

@[simp] theorem ofLinear_apply (g : Vector n F ≃ₗ[F] Vector n F)
    (hg : ∀ x y, form (g x) (g y) = form x y) (x : Vector n F) :
    ofLinear g hg • x = g x := LinearMap.toMatrix'_mulVec _ _

/-- Full isometries, not just a generated subgroup, correspond to the matrix model. -/
def isometryEquiv : Sp n F ≃ (form (n := n) (F := F)).IsometryEquiv (form (n := n) (F := F)) where
  toFun g := { toLinearEquiv := toLinear g, map_app' := preserves g }
  invFun g := ofLinear g.toLinearEquiv g.map_app'
  left_inv g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have h := congrFun (ofLinear_apply (toLinear g) (preserves g) (Pi.single j 1)) i
    simpa [smul_eq_mulVec, Matrix.mulVec_single] using h
  right_inv g := by
    apply DFunLike.ext
    intro x
    exact ofLinear_apply g.toLinearEquiv g.map_app' x

end Atlas.Symplectic
