import Theory.AtlasPort.LinearGroups.Symplectic.GeneratedAction
import Theory.AtlasPort.LinearGroups.Symplectic.PairStabilizer
set_option warningAsError false

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

/-- The actual complement group embeds by fixing the first hyperbolic plane. -/
def extendHom : Sp n F →* Sp (n+1) F :=
  (pairStabilizer n F).subtype.comp pairStabilizerEquiv.symm.toMonoidHom

@[simp] theorem extendHom_apply (g : Sp n F) : extendHom g = (extendPair g).val := rfl

/-- Extension takes a transvection to the same transvection in the larger space. -/
theorem extend_transvection (v : Vector n F) (a : F) :
    extendHom (transvection v a) = transvection ((headTail n).symm (0,v)) a := by
  apply ext_action
  intro x
  apply (headTail n).injective
  change headTail n (ofLinear (extendLinear (transvection v a))
    (extendLinear_preserves (transvection v a)) • x) = _
  rw [ofLinear_apply,extendLinear_headTail,transvection_apply,transvection_apply,
    map_add,map_smul,LinearEquiv.apply_symm_apply]
  have hf : form x ((headTail n).symm (0,v)) = form (headTail n x).2 v := by
    rw [form_headTail,LinearEquiv.apply_symm_apply]
    simp
  rw [hf]
  ext <;> simp

theorem extend_mem_generated {g : Sp n F} (hg : g ∈ transvectionGroup n F) :
    extendHom g ∈ transvectionGroup (n+1) F := by
  have hle : transvectionGroup n F ≤ (transvectionGroup (n+1) F).comap extendHom := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨v,a,rfl⟩
    change extendHom (transvection v a) ∈ transvectionGroup (n+1) F
    rw [extend_transvection]
    exact transvection_mem _ _
  exact hle hg

/-- Uniform full-group generation, without any order or simplicity premise. -/
theorem mem_transvectionGroup (n : ℕ) (g : Sp n F) : g ∈ transvectionGroup n F := by
  induction n with
  | zero =>
    rw [Subsingleton.elim g 1]
    exact (transvectionGroup 0 F).one_mem
  | succ n ih =>
    let e₀ : Vector (n+1) F := e 0
    let f₀ : Vector (n+1) F := f 0
    have hef : form e₀ f₀ = 1 := by simp [e₀,f₀,e]
    have he : e₀ ≠ 0 := by intro h; simp [h] at hef
    have hge : g • e₀ ≠ 0 := (smul_ne_zero_iff_ne g).mpr he
    obtain ⟨a,ha,hae⟩ := exists_generated_send hge he
    have hag : (a*g) • e₀ = e₀ := by rw [mul_smul,hae]
    have heu : form e₀ ((a*g) • f₀) = 1 := by
      have h := preserves (a*g) e₀ f₀
      change form ((a*g) • e₀) ((a*g) • f₀) = form e₀ f₀ at h
      rwa [hag,hef] at h
    obtain ⟨b,hb,hbe,hbf⟩ := exists_generated_send_fix hef heu
    let h : pairStabilizer n F := ⟨b*(a*g),by
      rw [mem_pairStabilizer]
      constructor
      · change (b*(a*g)) • e₀ = e₀
        rw [mul_smul,hag,hbe]
      · change (b*(a*g)) • f₀ = f₀
        rw [mul_smul,hbf]⟩
    have hh : h.val ∈ transvectionGroup (n+1) F := by
      have hh' := extend_mem_generated (ih (restrictPair h))
      simpa only [extendHom_apply,extend_restrict] using hh'
    have hfinal := (transvectionGroup (n+1) F).mul_mem
      ((transvectionGroup (n+1) F).inv_mem ha)
      ((transvectionGroup (n+1) F).mul_mem ((transvectionGroup (n+1) F).inv_mem hb) hh)
    simpa [h,mul_assoc] using hfinal

theorem transvectionGroup_eq_top : transvectionGroup n F = ⊤ := by
  apply top_unique
  intro g _
  exact mem_transvectionGroup n g

end Atlas.Symplectic
