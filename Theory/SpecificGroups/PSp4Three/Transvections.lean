module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# Symplectic transvections and their action

Characteristic-independent matrix and alternating-form proofs supporting the
concrete ternary simplicity theorem. This local module port is required because
the older shared symplectic ports are not Lean modules.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/Transvection.lean`, `Atlas/LinearGroups/Symplectic/TransvectionImage.lean`, `Atlas/LinearGroups/Symplectic/Isometry.lean`, `Atlas/LinearGroups/Symplectic/GeneratedAction.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

/-! Symplectic transvections in the original matrix carrier. No generation is assumed. -/
noncomputable section
namespace Matrix.PSp4Three
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
end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
open Matrix
variable {n : ℕ} {F : Type*} [Field F]

theorem exists_form_left {v : Vector n F} (hv : v ≠ 0) (a : F) :
    ∃ x, form x v = a := by
  obtain ⟨w,hw⟩ : ∃ w, form w v ≠ 0 := by
    by_contra! h
    exact hv (form_nondegenerate.2 v h)
  refine ⟨(a / form w v) • w, ?_⟩
  simp [map_smul, hw]

/-- The moved image is the actual direction line, without any generation premise. -/
theorem transvection_image {v : Vector n F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0) :
    LinearMap.range (transvectionMap v a - 1) = Submodule.span F {v} := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    have hv' : v ∈ Submodule.span F {v} := Submodule.subset_span (by simp)
    simpa only [LinearMap.sub_apply, transvectionMap_apply, Module.End.one_apply,
      add_sub_cancel_left] using (Submodule.span F {v}).smul_mem (a * form x v) hv'
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = v := Set.mem_singleton_iff.mp hx
    subst x
    obtain ⟨w,hw⟩ := exists_form_left hv a⁻¹
    refine ⟨w, ?_⟩
    simp [transvectionMap_apply, hw, ha]

theorem transvection_ne_one {v : Vector n F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0) :
    transvection v a ≠ 1 := by
  intro h
  obtain ⟨x,hx⟩ := exists_form_left hv 1
  have he := congrArg (fun g : Sp n F => g • x) h
  have hz : a • v = 0 := by simpa [transvection_apply, hx] using he
  exact (smul_ne_zero ha hv) hz

theorem transvection_send {x y : Vector n F} (h : form x y ≠ 0) :
    transvection (y-x) (form x y)⁻¹ • x = y := by
  simp [transvection_apply, map_sub, h]

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
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

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Subgroup generated by all genuine symplectic transvections. -/
def transvectionGroup (n : ℕ) (F : Type*) [Field F] : Subgroup (Sp n F) :=
  Subgroup.closure {g | ∃ (v : Vector n F) (a : F), g = transvection v a}

theorem transvection_mem (v : Vector n F) (a : F) : transvection v a ∈ transvectionGroup n F :=
  Subgroup.subset_closure ⟨v,a,rfl⟩

/-- Two nonzero linear functionals do not cover a vector space by their kernels,
also over the field with two elements. -/
theorem exists_pairing_both {x y : Vector n F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, form x z ≠ 0 ∧ form y z ≠ 0 := by
  obtain ⟨u,hu⟩ := Matrix.PSp4Three.Frame.exists_partner form form_nondegenerate hx
  obtain ⟨v,hv⟩ := Matrix.PSp4Three.Frame.exists_partner form form_nondegenerate hy
  by_cases hyu : form y u = 0
  · by_cases hxv : form x v = 0
    · refine ⟨u+v,?_,?_⟩ <;> simp [map_add,hu,hv,hyu,hxv]
    · exact ⟨v,hxv,by rw [hv]; exact one_ne_zero⟩
  · exact ⟨u,by rw [hu]; exact one_ne_zero,hyu⟩

/-- The generated subgroup is transitive on nonzero vectors in every characteristic. -/
theorem exists_generated_send {x y : Vector n F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g ∈ transvectionGroup n F, g • x = y := by
  obtain ⟨z,hxz,hyz⟩ := exists_pairing_both hx hy
  have hzy : form z y ≠ 0 := by rw [form_swap,neg_ne_zero]; exact hyz
  refine ⟨transvection (y-z) (form z y)⁻¹ * transvection (z-x) (form x z)⁻¹,
    (transvectionGroup n F).mul_mem (transvection_mem _ _) (transvection_mem _ _),?_⟩
  rw [mul_smul,transvection_send hxz,transvection_send hzy]

theorem transvection_fixes_of_orthogonal {e v : Vector n F} (hev : form e v = 0) (a : F) :
    transvection v a • e = e := by simp [transvection_apply,hev]

/-- Adjust the second vector of a hyperbolic pair while fixing the first. -/
theorem exists_generated_send_fix {e f u : Vector n F}
    (hef : form e f = 1) (heu : form e u = 1) :
    ∃ g ∈ transvectionGroup n F, g • e = e ∧ g • u = f := by
  have hue : form u e = -1 := by rw [form_swap,heu]
  by_cases huf : form u f = 0
  · let z := f+e
    have huz : form u z ≠ 0 := by simp [z,map_add,huf,hue]
    have hzf : form z f ≠ 0 := by simp [z,map_add,hef]
    have hezu : form e (z-u) = 0 := by simp [z,map_sub,map_add,hef,heu]
    have hefz : form e (f-z) = 0 := by simp [z]
    refine ⟨transvection (f-z) (form z f)⁻¹ * transvection (z-u) (form u z)⁻¹,
      (transvectionGroup n F).mul_mem (transvection_mem _ _) (transvection_mem _ _),?_,?_⟩
    · rw [mul_smul,transvection_fixes_of_orthogonal hezu,
        transvection_fixes_of_orthogonal hefz]
    · rw [mul_smul,transvection_send huz,transvection_send hzf]
  · refine ⟨transvection (f-u) (form u f)⁻¹,transvection_mem _ _,?_,transvection_send huf⟩
    apply transvection_fixes_of_orthogonal
    simp [map_sub,hef,heu]

end Matrix.PSp4Three
end
