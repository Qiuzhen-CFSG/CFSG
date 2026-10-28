import Theory.AtlasPort.LinearGroups.Symplectic.Transvection
set_option warningAsError false

noncomputable section
namespace Atlas.Symplectic
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

end Atlas.Symplectic
