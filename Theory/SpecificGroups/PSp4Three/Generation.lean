module

public import Theory.SpecificGroups.PSp4Three.Transvections

/-!
# Generation of the symplectic matrix group by transvections

Characteristic-independent matrix and alternating-form proofs supporting the
concrete ternary simplicity theorem. This local module port is required because
the older shared symplectic ports are not Lean modules.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/PairStabilizer.lean`, `Atlas/LinearGroups/Symplectic/Generation.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Pointwise stabilizer of the first hyperbolic pair, not of just one vector. -/
def pairStabilizer (n : ℕ) (F : Type*) [Field F] : Subgroup (Sp (n+1) F) :=
  MulAction.stabilizer (Sp (n+1) F) (e (n := n+1) (F := F) 0) ⊓ MulAction.stabilizer (Sp (n+1) F) (f (n := n+1) (F := F) 0)

theorem mem_pairStabilizer (g : Sp (n+1) F) : g ∈ pairStabilizer n F ↔
    g • e (n := n+1) (F := F) 0 = e (n := n+1) (F := F) 0 ∧ g • f (n := n+1) (F := F) 0 = f (n := n+1) (F := F) 0 := Iff.rfl

theorem pairStabilizer_head (g : pairStabilizer n F) (x : Vector (n+1) F) :
    (headTail n (g.val • x)).1 = (headTail n x).1 := by
  have he := preserves g.val x (e (n := n+1) (F := F) 0)
  have hf := preserves g.val x (f (n := n+1) (F := F) 0)
  change form (g.val • x) (g.val • e (n := n+1) (F := F) 0) = form x (e (n := n+1) (F := F) 0) at he
  change form (g.val • x) (g.val • f (n := n+1) (F := F) 0) = form x (f (n := n+1) (F := F) 0) at hf
  rw [(mem_pairStabilizer g.val).mp g.prop |>.1] at he
  rw [(mem_pairStabilizer g.val).mp g.prop |>.2] at hf
  simp only [form_e_right, neg_inj] at he
  simp only [form_f_right] at hf
  exact Prod.ext hf he

/-- Restriction to the actual orthogonal complement, in its retained coordinates. -/
def tailMap (g : pairStabilizer n F) : Vector n F →ₗ[F] Vector n F :=
  (LinearMap.snd F (F×F) (Vector n F)).comp ((headTail n).toLinearMap.comp
    ((toLinear g.val).toLinearMap.comp ((headTail n).symm.toLinearMap.comp
      (LinearMap.inr F (F×F) (Vector n F)))))

theorem tailMap_apply (g : pairStabilizer n F) (x : Vector n F) :
    tailMap g x = (headTail n (g.val • (headTail n).symm (0,x))).2 := rfl

theorem pairStabilizer_tail (g : pairStabilizer n F) (x : Vector n F) :
    headTail n (g.val • (headTail n).symm (0,x)) = (0,tailMap g x) := by
  apply Prod.ext
  · rw [pairStabilizer_head, LinearEquiv.apply_symm_apply]
  · rfl

theorem tailMap_mul (g h : pairStabilizer n F) (x : Vector n F) :
    tailMap (g*h) x = tailMap g (tailMap h x) := by
  rw [tailMap_apply, tailMap_apply g]; simp only [Subgroup.coe_mul, mul_smul]
  rw [← pairStabilizer_tail h x, LinearEquiv.symm_apply_apply]

@[simp] theorem tailMap_one (x : Vector n F) : tailMap (1 : pairStabilizer n F) x = x := by
  simp [tailMap_apply]

def tailLinear (g : pairStabilizer n F) : Vector n F ≃ₗ[F] Vector n F :=
  { tailMap g with
    invFun := tailMap g⁻¹
    left_inv := fun x => by
      change tailMap g⁻¹ (tailMap g x) = x
      rw [← tailMap_mul, inv_mul_cancel, tailMap_one]
    right_inv := fun x => by
      change tailMap g (tailMap g⁻¹ x) = x
      rw [← tailMap_mul, mul_inv_cancel, tailMap_one] }

theorem tailLinear_preserves (g : pairStabilizer n F) (x y : Vector n F) :
    form (tailLinear g x) (tailLinear g y) = form x y := by
  have h := preserves g.val ((headTail n).symm (0,x)) ((headTail n).symm (0,y))
  change form (g.val • (headTail n).symm (0,x)) (g.val • (headTail n).symm (0,y)) = _ at h
  rw [form_headTail, form_headTail, pairStabilizer_tail, pairStabilizer_tail,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  simpa [tailLinear] using h

def restrictPair (g : pairStabilizer n F) : Sp n F :=
  ofLinear (tailLinear g) (tailLinear_preserves g)

@[simp] theorem restrictPair_apply (g : pairStabilizer n F) (x : Vector n F) :
    restrictPair g • x = tailMap g x := ofLinear_apply _ _ _

/-- Extend a full smaller symplectic isometry by the identity on the hyperbolic plane. -/
def extendLinear (g : Sp n F) : Vector (n+1) F ≃ₗ[F] Vector (n+1) F :=
  ((headTail n).trans ((LinearEquiv.refl F (F×F)).prodCongr (toLinear g))).trans
    (headTail n).symm

theorem extendLinear_headTail (g : Sp n F) (x : Vector (n+1) F) :
    headTail n (extendLinear g x) = ((headTail n x).1,g • (headTail n x).2) := by
  simp [extendLinear]

theorem extendLinear_preserves (g : Sp n F) (x y : Vector (n+1) F) :
    form (extendLinear g x) (extendLinear g y) = form x y := by
  rw [form_headTail, extendLinear_headTail, extendLinear_headTail, form_headTail x y]
  simp only [smul_eq_mulVec, preserves]

def extendPair (g : Sp n F) : pairStabilizer n F :=
  ⟨ofLinear (extendLinear g) (extendLinear_preserves g), by
    rw [mem_pairStabilizer]; constructor <;> rw [ofLinear_apply] <;> apply (headTail n).injective <;>
      rw [extendLinear_headTail] <;> simp [headTail,e,f] <;>
        change toLinear g 0 = 0 <;> exact map_zero _⟩

@[simp] theorem restrict_extend (g : Sp n F) : restrictPair (extendPair g) = g := by
  apply ext_action
  intro x
  rw [restrictPair_apply, tailMap_apply]
  change (headTail n (ofLinear (extendLinear g) (extendLinear_preserves g) • _)).2 = _
  rw [ofLinear_apply, extendLinear_headTail, LinearEquiv.apply_symm_apply]

@[simp] theorem headTail_e : headTail n (e (n := n+1) (F := F) 0) = ((1,0),0) := by
  simp [headTail,e]
  rfl

@[simp] theorem headTail_f : headTail n (f (n := n+1) (F := F) 0) = ((0,1),0) := by
  simp [headTail,f]
  rfl

theorem headTail_decomposition (x : Vector (n+1) F) :
    x = (headTail n x).1.1 • e 0 + (headTail n x).1.2 • f 0 +
      (headTail n).symm (0,(headTail n x).2) := by
  apply (headTail n).injective
  simp only [map_add, map_smul, headTail_e, headTail_f, LinearEquiv.apply_symm_apply]
  ext <;> simp

theorem pairStabilizer_block (g : pairStabilizer n F) (x : Vector (n+1) F) :
    headTail n (g.val • x) = ((headTail n x).1,tailMap g (headTail n x).2) := by
  have h := congrArg (fun z => headTail n (toLinear g.val z)) (headTail_decomposition x)
  simp only [map_add, map_smul, toLinear_apply,
    (mem_pairStabilizer g.val).mp g.prop |>.1,
    (mem_pairStabilizer g.val).mp g.prop |>.2,
    headTail_e, headTail_f, pairStabilizer_tail] at h
  simpa using h

@[simp] theorem extend_restrict (g : pairStabilizer n F) : extendPair (restrictPair g) = g := by
  apply Subtype.ext
  apply ext_action
  intro x
  apply (headTail n).injective
  change headTail n (ofLinear (extendLinear (restrictPair g)) (extendLinear_preserves (restrictPair g)) • x) = _
  rw [ofLinear_apply, extendLinear_headTail, restrictPair_apply, pairStabilizer_block]

/-- The full pointwise stabilizer is the full smaller symplectic group. -/
def pairStabilizerEquiv : pairStabilizer n F ≃* Sp n F where
  toFun := restrictPair
  invFun := extendPair
  left_inv := extend_restrict
  right_inv := restrict_extend
  map_mul' g h := by
    apply ext_action
    intro x
    rw [restrictPair_apply, mul_smul, restrictPair_apply, restrictPair_apply, tailMap_mul]

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
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

end Matrix.PSp4Three
end
