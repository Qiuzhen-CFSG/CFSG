import Theory.AtlasPort.LinearGroups.Symplectic.Basic
import Mathlib.LinearAlgebra.Transvection.Basic
set_option warningAsError false

/-! Symplectic transvections in the original matrix carrier. No generation is assumed. -/
noncomputable section
namespace Atlas.Symplectic
open Matrix
variable {n : ℕ} {F : Type*} [CommRing F]

/-- x ↦ x + a β(x,v) v, represented by the library's general transvection. -/
def transvectionMap (v : Vector n F) (a : F) : Module.End F (Vector n F) :=
  LinearMap.transvection (a • (form (n := n) (F := F)).flip v) v

@[simp] theorem transvectionMap_apply (v : Vector n F) (a : F) (x : Vector n F) :
    transvectionMap v a x = x + (a * form x v) • v := rfl

theorem transvectionMap_preserves (v : Vector n F) (a : F) (x y : Vector n F) :
    form (transvectionMap v a x) (transvectionMap v a y) = form x y := by
  simp only [transvectionMap_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, form_self, mul_zero, add_zero]
  rw [form_swap v y]
  ring

def transvection (v : Vector n F) (a : F) : Sp n F :=
  ⟨LinearMap.toMatrix' (transvectionMap v a), mem_iff_preserves.mpr (by
    intro x y
    simpa only [LinearMap.toMatrix'_mulVec] using transvectionMap_preserves v a x y)⟩

@[simp] theorem transvection_apply (v : Vector n F) (a : F) (x : Vector n F) :
    transvection v a • x = x + (a * form x v) • v := by
  change (LinearMap.toMatrix' (transvectionMap v a)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, transvectionMap_apply]

/-- Matrix elements are determined by the natural faithful action. -/
theorem ext_action {g h : Sp n F} (he : ∀ x : Vector n F, g • x = h • x) : g = h :=
  FaithfulSMul.eq_of_smul_eq_smul he

@[simp] theorem transvection_zero (v : Vector n F) : transvection v (0 : F) = 1 := by
  apply ext_action
  intro x
  simp only [transvection_apply, zero_mul, zero_smul, add_zero, one_smul]

@[simp] theorem transvection_zero_vector (a : F) : transvection (0 : Vector n F) a = 1 := by
  apply ext_action
  intro x
  simp only [transvection_apply, smul_zero, add_zero, one_smul]

theorem transvection_add (v : Vector n F) (a b : F) :
    transvection v (a+b) = transvection v a * transvection v b := by
  apply ext_action
  intro x
  simp only [mul_smul, transvection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, form_self, mul_zero, add_zero]
  simp only [add_smul]
  abel

@[simp] theorem transvection_inverse (v : Vector n F) (a : F) :
    (transvection v a)⁻¹ = transvection v (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← transvection_add, add_neg_cancel, transvection_zero]

theorem transvection_scale (v : Vector n F) (a c : F) :
    transvection (c • v) a = transvection v (c^2*a) := by
  apply ext_action
  intro x
  simp only [transvection_apply, map_smul, smul_eq_mul, smul_smul]
  congr 1
  congr 1
  ring

theorem transvection_conjugate (g : Sp n F) (v : Vector n F) (a : F) :
    g * transvection v a * g⁻¹ = transvection (g • v) a := by
  apply ext_action
  intro x
  simp only [mul_smul]
  simp only [transvection_apply]
  change g.val *ᵥ ((g⁻¹ • x) + (a * form (g⁻¹ • x) v) • v) = _
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  change g • (g⁻¹ • x) + (a * form (g⁻¹ • x) v) • (g • v) = _
  rw [smul_inv_smul]
  have hp := preserves g (g⁻¹ • x) v
  change form (g • (g⁻¹ • x)) (g • v) = _ at hp
  rw [smul_inv_smul] at hp
  rw [hp]

theorem transvection_commute {u v : Vector n F} (h : form u v = 0) (a b : F) :
    Commute (transvection u a) (transvection v b) := by
  have h' : form v u = 0 := by rw [form_swap, h, neg_zero]
  apply ext_action
  intro x
  simp only [mul_smul, transvection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, h, h', mul_zero, add_zero]
  abel
end Atlas.Symplectic
