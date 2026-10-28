module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitPBW
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups

/-!
# Field automorphisms of hyperbolic isometry groups

A field automorphism acts coordinatewise on the standard hyperbolic space.
Conjugating a linear isometry by this semilinear coordinate map gives another
linear isometry, since the hyperbolic quadratic form has integral coefficients.
This defines an automorphism of the full quadratic-isometry point group in
arbitrary characteristic. No claim of algebraic regularity is made for an
arbitrary field automorphism.

This is the coordinate input to the ordinary Frobenius construction in GLS3,
§1.15 and §2.1, specialized later to the split D4 Spin carrier.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
universe u

namespace Theory.AlgebraicGroup.HyperbolicFieldAutomorphisms

variable {k : Type u} [Field k]

def coordinates (r : ℕ) (σ : k ≃+* k) :
    HyperbolicSpace k r ≃+ HyperbolicSpace k r where
  toFun v := (fun i => σ (v.1 i), fun i => σ (v.2 i))
  invFun v := (fun i => σ.symm (v.1 i), fun i => σ.symm (v.2 i))
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by ext <;> simp

theorem coordinates_smul (r : ℕ) (σ : k ≃+* k) (a : k) (v : HyperbolicSpace k r) :
    coordinates r σ (a • v) = σ a • coordinates r σ v := by
  ext <;> simp [coordinates]

theorem coordinates_form (r : ℕ) (σ : k ≃+* k) (v : HyperbolicSpace k r) :
    hyperbolicForm r (coordinates r σ v) = σ (hyperbolicForm r v) := by
  simp [hyperbolicForm_apply, coordinates, map_sum, map_mul]

@[simp] theorem coordinates_symm_apply (r : ℕ) (σ : k ≃+* k)
    (v : HyperbolicSpace k r) :
    coordinates r σ.symm (coordinates r σ v) = v := by
  ext <;> simp [coordinates]

@[simp] theorem coordinates_apply_symm (r : ℕ) (σ : k ≃+* k)
    (v : HyperbolicSpace k r) :
    coordinates r σ (coordinates r σ.symm v) = v := by
  ext <;> simp [coordinates]

def conjugateLinear (r : ℕ) (σ : k ≃+* k)
    (g : HyperbolicSpace k r ≃ₗ[k] HyperbolicSpace k r) :
    HyperbolicSpace k r ≃ₗ[k] HyperbolicSpace k r where
  toFun v := coordinates r σ (g (coordinates r σ.symm v))
  invFun v := coordinates r σ (g.symm (coordinates r σ.symm v))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp
  map_smul' a v := by simp [coordinates_smul]

@[simp] theorem conjugateLinear_apply (r : ℕ) (σ : k ≃+* k)
    (g : HyperbolicSpace k r ≃ₗ[k] HyperbolicSpace k r) (v : HyperbolicSpace k r) :
    conjugateLinear r σ g v = coordinates r σ (g (coordinates r σ.symm v)) := rfl

def orthogonal (r : ℕ) (σ : k ≃+* k) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) r) ≃*
      quadraticIsometrySubgroup (hyperbolicForm (k := k) r) where
  toFun g := ⟨conjugateLinear r σ g.1, by
    apply (mem_quadraticIsometrySubgroup _ _).2
    intro v
    change hyperbolicForm r (coordinates r σ (g.1 (coordinates r σ.symm v))) = _
    rw [coordinates_form, (mem_quadraticIsometrySubgroup _ _).1 g.2,
      coordinates_form, σ.apply_symm_apply]⟩
  invFun g := ⟨conjugateLinear r σ.symm g.1, by
    apply (mem_quadraticIsometrySubgroup _ _).2
    intro v
    change hyperbolicForm r (coordinates r σ.symm (g.1 (coordinates r σ v))) = _
    rw [coordinates_form, (mem_quadraticIsometrySubgroup _ _).1 g.2,
      coordinates_form, σ.symm_apply_apply]⟩
  left_inv g := by apply Subtype.ext; ext v <;> simp
  right_inv g := by apply Subtype.ext; ext v <;> simp
  map_mul' g h := by apply Subtype.ext; ext v <;> simp [LinearEquiv.mul_apply]

@[simp] theorem orthogonal_apply (r : ℕ) (σ : k ≃+* k)
    (g : quadraticIsometrySubgroup (hyperbolicForm (k := k) r))
    (v : HyperbolicSpace k r) :
    (orthogonal r σ g).1 v = coordinates r σ (g.1 (coordinates r σ.symm v)) := rfl

end Theory.AlgebraicGroup.HyperbolicFieldAutomorphisms
