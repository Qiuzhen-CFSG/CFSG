/-
Authors: Yusen Tang
-/

module

public import Submission.FeitThompson.Representation.RepMap

open Function

namespace Representation

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module F V] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)
  (f : V ≃ₗ[F] W)

/-- Predicate asserting that a linear equivalence intertwines two representations. -/
@[mk_iff]
public structure IsIntertwiningEquiv : Prop where
  isIntertwining (g : G) (v : V) : f (ρ g v) = σ g (f v)

/-- Bundled linear equivalences intertwining the actions of two representations. -/
@[ext]
public structure RepEquiv extends V ≃ₗ[F] W where
  isIntertwining' : ∀ (g : G), toLinearEquiv ∘ₗ ρ g = σ g ∘ₗ toLinearEquiv

/-- Notation for bundled intertwining linear equivalences. -/
notation:25 ρ " ≃ₗ " σ:0 => RepEquiv ρ σ

namespace RepEquiv

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module F V] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}
  (f : ρ ≃ₗ σ)

/-- The underlying intertwining map of a representation equivalence. -/
@[expose]
public def toRepMap (e : ρ ≃ₗ σ) : ρ →ₗ σ :=
  RepMap.mk e.toLinearMap e.isIntertwining'

public instance : Coe (ρ ≃ₗ σ) (ρ →ₗ σ) where
  coe := fun e ↦ e.toRepMap

public theorem toRepMap_injective : (toRepMap : (ρ ≃ₗ σ) → (ρ →ₗ σ)).Injective :=
  fun x y h ↦ by
  ext v
  · show x.toRepMap v = y.toRepMap v
    exact RepMap.congr_fun h v
  · have : x.toEquiv.symm v = y.toEquiv.symm v := by
      rw [Equiv.symm_apply_eq]
      show v = x.toRepMap (y.toEquiv.symm v)
      rw [h]
      show v = y.toEquiv (y.toEquiv.symm v)
      simp only [LinearEquiv.coe_symm_toEquiv, LinearEquiv.coe_toEquiv,
        LinearEquiv.apply_symm_apply]
    exact this

@[simp]
public theorem toRepMap_inj {e₁ e₂ : ρ ≃ₗ σ} : e₁.toRepMap = e₂.toRepMap ↔ e₁ = e₂ :=
  toRepMap_injective.eq_iff


public instance : EquivLike (ρ ≃ₗ σ) V W where
  coe e := e.toFun
  inv e := e.toLinearEquiv.symm.toFun
  coe_injective' _ _ h h1 := RepEquiv.ext h h1
  left_inv e x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  right_inv e x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

public theorem coe_injective : @Injective (ρ ≃ₗ σ) (V → W) DFunLike.coe :=
  DFunLike.coe_injective

section

variable (e e' : ρ ≃ₗ σ)

@[simp]
public theorem coe_coe : ⇑(e : ρ →ₗ σ) = e :=
  rfl

public theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

public theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl

public theorem toFun_eq_coe : e.toFun = e := List.map_inj.mp rfl

section

variable {e e'}

@[ext]
public theorem ext' (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

public protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

public protected theorem congr_fun (h : e = e') (x : V) : e x = e' x :=
  DFunLike.congr_fun h x

public theorem isIntertwining (e : ρ ≃ₗ σ) : ∀ (g : G) (v : V), e (ρ g v) = σ g (e v) :=
  e.toRepMap.isIntertwining

end

section

variable (ρ)

/-- The identity equivalence of a representation. -/
@[expose, refl]
public def refl : ρ ≃ₗ ρ :=
  { LinearMap.id, Equiv.refl ρ with
    isIntertwining' g:= by
      ext v
      simp only [LinearMap.id_comp, LinearMap.comp_id]
       }

end

@[simp]
public theorem refl_apply (x : V) : refl ρ x = x :=
  rfl

/-- The inverse of a representation equivalence. -/
@[expose, symm]
public def symm (e : ρ ≃ₗ σ) : σ ≃ₗ ρ :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    isIntertwining' g:= by
      ext v
      show e.toEquiv.symm ((σ g) v) = (ρ g) (e.toEquiv.symm v)
      rw [Equiv.symm_apply_eq]
      have : e.toEquiv ((ρ g) (e.toEquiv.symm v)) = (σ g) (e.toEquiv (e.toEquiv.symm v)) := (e.isIntertwining) g (e.toEquiv.symm v)
      simp only [LinearEquiv.coe_symm_toEquiv, LinearEquiv.coe_toEquiv,
        LinearEquiv.apply_symm_apply] at this
      rw [← this]
      rfl}

/-! Projections used by `simps` for `RepEquiv`. -/

/-- Forward application projection for `RepEquiv`. -/
@[expose]
public def Simps.apply (e : ρ ≃ₗ σ) : V → W :=
  e

/-- Inverse application projection for `RepEquiv`. -/
@[expose]
public def Simps.symm_apply (e : ρ ≃ₗ σ) : W → V :=
  e.symm

initialize_simps_projections RepEquiv (toFun → apply, invFun → symm_apply)

public theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

public theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
public theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

public theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm := rfl

variable {F G V W X Y : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid X] [AddCommMonoid Y] [Module F V] [Module F W] [Module F X]
  [Module F Y] {ρ : Representation F G V} {σ : Representation F G W}
  {ϕ : Representation F G X} {φ : Representation F G Y}
variable (e₁₂ : ρ ≃ₗ σ) (e₂₃ : σ ≃ₗ ϕ)

/-! Composition operations on representation equivalences. -/

/-- Composition of representation equivalences. -/
@[expose, trans, nolint unusedArguments]
public def trans : ρ ≃ₗ ϕ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with
    isIntertwining' g:= by
      ext v
      show e₂₃ (e₁₂ ((ρ g) v)) = (ϕ g) (e₂₃ (e₁₂ v))
      rw [e₁₂.isIntertwining , e₂₃.isIntertwining]}

/-! `symm` as an equivalence on equivalences. -/

/-- Taking inverses defines an equivalence between `ρ ≃ₗ σ` and `σ ≃ₗ ρ`. -/
@[expose, simps!]
public def symmEquiv : (ρ ≃ₗ σ) ≃ (σ ≃ₗ ρ) where
  toFun := .symm
  invFun := .symm

variable {e₁₂} {e₂₃} {e : ρ ≃ₗ σ}

@[simp]
public theorem trans_apply (c : V) : (e₁₂.trans e₂₃) c = e₂₃ (e₁₂ c) :=
  rfl

public theorem coe_trans :
    (e₁₂.trans e₂₃).toRepMap = e₂₃.toRepMap.comp e₁₂:=
  rfl

@[simp]
public theorem apply_symm_apply (c : W) : e (e.symm c) = c :=
  e.right_inv c

@[simp]
public theorem symm_apply_apply (b : V) : e.symm (e b) = b :=
  e.left_inv b

public theorem comp_symm : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id :=
  LinearMap.ext e.apply_symm_apply

public theorem symm_comp : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
  LinearMap.ext e.symm_apply_apply

public lemma comp_symm_assoc (f : ϕ →ₗ σ):
    e₁₂.toRepMap ∘ e₁₂.symm.toRepMap ∘ f = f := by ext; simp

public lemma symm_comp_assoc (f : ϕ →ₗ ρ):
    e₁₂.symm.toRepMap ∘ e₁₂.toRepMap ∘ f = f := by ext; simp

@[simp]
public theorem trans_symm : (e₁₂.trans e₂₃ : ρ ≃ₗ ϕ).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl

public theorem symm_trans_apply (c : X) :
    (e₁₂.trans e₂₃ : ρ ≃ₗ ϕ).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl

@[simp]
public theorem trans_refl : e.trans (refl σ) = e :=
  rfl

@[simp]
public theorem refl_trans : (refl ρ).trans e = e :=
  rfl

public theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

public theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

public theorem eq_comp_symm {α : Type*} (f : W → α) (g : V → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g

public theorem comp_symm_eq {α : Type*} (f : W → α) (g : V → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g

public theorem eq_symm_comp {α : Type*} (f : α → V) (g : α → W) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g

public theorem symm_comp_eq {α : Type*} (f : α → V) (g : α → W) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g

@[simp]
public theorem comp_coe (f : ρ ≃ₗ σ) (f' : σ ≃ₗ ϕ) :
    f'.toRepMap.comp f.toRepMap = (f.trans f').toRepMap :=
  rfl

public lemma trans_assoc (e₁₂ : ρ ≃ₗ σ) (e₂₃ : σ ≃ₗ ϕ) (e₃₄ : ϕ ≃ₗ φ) :
    (e₁₂.trans e₂₃).trans e₃₄ = e₁₂.trans (e₂₃.trans e₃₄) := rfl

public theorem eq_comp_toRepMap_symm (f : σ →ₗ ϕ) (g : ρ →ₗ ϕ) :
    f = g.comp e₁₂.symm.toRepMap ↔ f.comp e₁₂.toRepMap = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

public theorem comp_toRepMap_symm_eq (f : σ →ₗ ϕ) (g : ρ →ₗ ϕ) :
    g.comp e₁₂.symm.toRepMap = f ↔ g = f.comp e₁₂.toRepMap := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

public theorem eq_toRepMap_symm_comp (f : ϕ →ₗ ρ) (g : ϕ →ₗ σ) :
    f = e₁₂.symm.toRepMap.comp g ↔ e₁₂.toRepMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

public theorem toRepMap_symm_comp_eq (f : ϕ →ₗ ρ) (g : ϕ →ₗ σ) :
    e₁₂.symm.toRepMap.comp g = f ↔ g = e₁₂.toRepMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

@[simp]
public theorem comp_toRepMap_eq_iff (f g : ϕ →ₗ ρ) :
    e₁₂.toRepMap.comp f = e₁₂.toRepMap.comp g ↔ f = g := by
  refine ⟨fun h => ?_, ?_⟩
  rw [← (toRepMap_symm_comp_eq g (e₁₂.toRepMap.comp f)).mpr h, eq_toRepMap_symm_comp]
  exact fun a ↦
    RepMap.toLinearMap_injective (e₁₂.toRepMap.comp f) (e₁₂.toRepMap.comp g)
      (congrArg IntertwiningMap.toLinearMap (congrArg e₁₂.toRepMap.comp a))

@[simp]
public theorem eq_comp_toRepMap_iff (f g : σ →ₗ ϕ) :
    f.comp e₁₂.toRepMap = g.comp e₁₂.toRepMap ↔ f = g := by
  refine ⟨fun h => ?_, fun a ↦ congrFun (congrArg RepMap.comp a) e₁₂.toRepMap⟩
  rw [(eq_comp_toRepMap_symm g (f.comp e₁₂.toRepMap)).mpr h.symm, eq_comp_toRepMap_symm]

public lemma comp_symm_cancel_left (e : ρ ≃ₗ σ) (f : ϕ →ₗ σ) :
    e.toRepMap ∘ (e.symm.toRepMap ∘ f) = f := by ext; simp

public lemma symm_comp_cancel_left (e : ρ ≃ₗ σ) (f : ϕ →ₗ ρ) :
    e.symm.toRepMap ∘ (e.toRepMap ∘ f) = f := by ext; simp

public lemma comp_symm_cancel_right (e : ρ ≃ₗ σ) (f : σ →ₗ ϕ) :
    (f ∘ e.toRepMap) ∘ e.symm.toRepMap = f := by ext; simp

public lemma symm_comp_cancel_right (e : ρ ≃ₗ σ) (f : ρ →ₗ ϕ) :
    (f ∘ e.symm.toRepMap) ∘ e.toRepMap = f := by ext; simp

public lemma trans_symm_cancel_left (e : ρ ≃ₗ σ) (f : ρ ≃ₗ ϕ) :
    e.trans (e.symm.trans f) = f := by ext; simp

public lemma symm_trans_cancel_left (e : ρ ≃ₗ σ) (f : σ ≃ₗ ϕ) :
    e.symm.trans (e.trans f) = f := by ext; simp

public lemma trans_symm_cancel_right (e : ρ ≃ₗ σ) (f : ϕ ≃ₗ ρ) :
    (f.trans e).trans e.symm = f := by ext; simp

public lemma symm_trans_cancel_right (e : ρ ≃ₗ σ) (f : ϕ ≃ₗ σ) :
    (f.trans e.symm).trans e = f := by ext; simp

@[simp]
public theorem refl_symm : (refl ρ).symm = RepEquiv.refl ρ :=
  rfl

@[simp]
public theorem self_trans_symm (f : ρ ≃ₗ σ) : f.trans f.symm = RepEquiv.refl ρ := by
  ext x
  simp

@[simp]
public theorem symm_trans_self (f : ρ ≃ₗ σ) : f.symm.trans f = RepEquiv.refl σ := by
  ext x
  simp

@[simp]
public theorem refl_toLinearMap : (RepEquiv.refl ρ).toRepMap = RepMap.id :=
  rfl

@[simp]
public theorem mk_coe (h) : (RepEquiv.mk e.toLinearEquiv h) = e := rfl

public protected theorem map_add (a b : V) : e (a + b) = e a + e b :=
  LinearEquiv.map_add e.toLinearEquiv a b

public protected theorem map_zero : e 0 = 0 :=
  LinearEquiv.map_zero e.toLinearEquiv

public theorem map_smul (c : F) (x : V) : e (c • x) = c • e x :=
  LinearEquiv.map_smul e.toLinearEquiv c x

public theorem map_eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff

public theorem map_ne_zero_iff {x : V} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff

@[simp]
public theorem symm_symm : e.symm.symm = e := rfl

public theorem symm_bijective:
    Function.Bijective (symm : (ρ ≃ₗ σ) → (σ ≃ₗ ρ)) :=
  Function.bijective_iff_has_inverse.mpr ⟨symm, fun _ ↦ symm_symm, fun _ ↦ symm_symm⟩

public protected theorem bijective : Function.Bijective e :=
  e.toEquiv.bijective

public protected theorem injective : Function.Injective e :=
  e.toEquiv.injective

public protected theorem surjective : Function.Surjective e :=
  e.toEquiv.surjective

public protected theorem image_eq_preimage_symm (s : Set V) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

public protected theorem image_symm_eq_preimage (s : Set W) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage_symm s

variable {F G V W : Type*} [Field F] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}

lemma irreducible_of_euqiv {ρ : Representation F G V} {σ : Representation F G W} (f : ρ ≃ₗ σ) :
    IsIrreducible σ → IsIrreducible ρ := fun h ↦ by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial V := (Equiv.nontrivial_congr f.toEquiv).mpr this
  exact RepMap.irreducible_of_inj (f := f.toRepMap) f.injective

public theorem irreducible_euqiv {ρ : Representation F G V} {σ : Representation F G W} (f : ρ ≃ₗ σ) :
    IsIrreducible ρ ↔ IsIrreducible σ :=
  ⟨irreducible_of_euqiv f.symm, irreducible_of_euqiv f⟩

public theorem irreducible_of_group_iso {H : Type*} [Monoid H] {ρ : Representation F G V} {σ : Representation F H V} (f : G ≃* H) (h : ∀ g : G, ∀ v : V, ρ g v = σ (f g) v):
    IsIrreducible ρ → IsIrreducible σ := fun h1 ↦ by
  unfold IsIrreducible
  rw [isSimpleOrder_iff]
  constructor
  · let := Subrepresentation.irreducible_module_nontrivial ρ
    exact Subrepresentation.module_nontrival
  · intro u
    let v : Subrepresentation ρ := {
      toSubmodule := u.toSubmodule
      apply_mem_toSubmodule g v hv := by
        rw [h]
        exact u.apply_mem_toSubmodule (f g) hv
    }
    unfold IsIrreducible at h1
    rw [isSimpleOrder_iff] at h1
    have h := h1.2 v
    have : u = ⊥ ↔ v = ⊥ := by
      have : u.toSubmodule = ⊥ ↔ u = ⊥ := StrictMono.apply_eq_bot_iff fun ⦃a b⦄ c ↦ c
      rw [← this]
      have : v.toSubmodule = ⊥ ↔ v = ⊥ := StrictMono.apply_eq_bot_iff fun ⦃a b⦄ c ↦ c
      rw [← this]
    rw [this]
    have : u = ⊤ ↔ v = ⊤ := by
      have : u.toSubmodule = ⊤ ↔ u = ⊤ := StrictMono.apply_eq_top_iff fun ⦃a b⦄ c ↦ c
      rw [← this]
      have : v.toSubmodule = ⊤ ↔ v = ⊤ := StrictMono.apply_eq_top_iff fun ⦃a b⦄ c ↦ c
      rw [← this]
    rw [this]
    exact h

public theorem irreducible_iff_group_iso {H : Type*} [Monoid H] {ρ : Representation F G V} {σ : Representation F H V} (f : G ≃* H) (h : ∀ g : G, ∀ v : V, ρ g v = σ (f g) v):
    IsIrreducible ρ ↔ IsIrreducible σ := by
  have h' : ∀ g : H, ∀ v : V, σ g v = ρ (f.symm g) v := fun _ _ ↦ by
    simp_all only [MulEquiv.apply_symm_apply]
  refine ⟨irreducible_of_group_iso f h, irreducible_of_group_iso f.symm h'⟩


end

/-- Convert Mathlib's representation equivalence to the project bundled
representation equivalence. -/
public noncomputable def ofRepresentationEquiv
    {F G V W : Type*} [CommRing F] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [Module F V] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : Representation.Equiv ρ σ) : ρ ≃ₗ σ :=
  Representation.RepEquiv.mk e.toLinearEquiv e.isIntertwining'

/-- Convert the project bundled representation equivalence to Mathlib's
representation equivalence. -/
public noncomputable def toRepresentationEquiv
    {F G V W : Type*} [CommRing F] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [Module F V] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : ρ ≃ₗ σ) : Representation.Equiv ρ σ :=
  Representation.Equiv.mk e.toLinearEquiv e.isIntertwining'
end RepEquiv

