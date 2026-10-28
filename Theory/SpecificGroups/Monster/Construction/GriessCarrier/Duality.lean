module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Data.Real.Basic

/-!
# Recovering a Griess product and its stabilizer from the forms

A positive bilinear form is nondegenerate. On a finite-dimensional real
space its duality isomorphism turns a trilinear form into a unique bilinear
product. Symmetry gives commutativity and associativity of the form, and
an isometry preserves the trilinear form exactly when it preserves this
product. Both simultaneous stabilizers are actual subgroups of linear
equivalences.

These are general duality lemmas. They do not choose a Griess space or its
forms: the final carrier must supply the fixed Section 27 space and the
five blocks from Section 28.

Source: Aschbacher, *Sporadic Groups*, 9.4(3) and 28.12, printed p. 154.
-/

@[expose] public section

namespace Sporadic.Monster.Construction.Griess

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev TrilinearForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ

/-- Positive definiteness supplies both nondegeneracy conditions. -/
theorem nondegenerate_of_positive (γ : LinearMap.BilinForm ℝ V)
    (hγ : ∀ x : V, x ≠ 0 → 0 < γ x x) : γ.Nondegenerate := by
  constructor
  · intro x hx
    by_contra h
    exact (ne_of_gt (hγ x h)) (hx x)
  · intro x hx
    by_contra h
    exact (ne_of_gt (hγ x h)) (hx x)

variable [FiniteDimensional ℝ V]

/-- Recover the bilinear multiplication from the third-slot dual functional. -/
noncomputable def dualProduct (γ : LinearMap.BilinForm ℝ V) (hγ : γ.Nondegenerate)
    (β : TrilinearForm V) : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  β.compr₂ (γ.toDual hγ).symm.toLinearMap

@[simp] theorem gamma_dualProduct (γ : LinearMap.BilinForm ℝ V) (hγ : γ.Nondegenerate)
    (β : TrilinearForm V) (x y z : V) :
    γ (dualProduct γ hγ β x y) z = β x y z :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := hγ) (β x y) z

theorem dualProduct_unique (γ : LinearMap.BilinForm ℝ V) (hγ : γ.Nondegenerate)
    (β : TrilinearForm V) (m : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hm : ∀ x y z, γ (m x y) z = β x y z) : m = dualProduct γ hγ β := by
  ext x y
  apply (γ.toDual hγ).injective
  ext z
  exact (hm x y z).trans (gamma_dualProduct γ hγ β x y z).symm

theorem dualProduct_comm (γ : LinearMap.BilinForm ℝ V) (hγ : γ.Nondegenerate)
    (β : TrilinearForm V) (hβ : ∀ x y z, β x y z = β y x z) (x y : V) :
    dualProduct γ hγ β x y = dualProduct γ hγ β y x := by
  apply (γ.toDual hγ).injective
  ext z
  exact (gamma_dualProduct γ hγ β x y z).trans
    ((hβ x y z).trans (gamma_dualProduct γ hγ β y x z).symm)

/-- Associativity of the form, which does not assert associativity of the product. -/
theorem dualProduct_invariant_form (γ : LinearMap.BilinForm ℝ V)
    (hγ : γ.Nondegenerate) (hs : ∀ x y, γ x y = γ y x)
    (β : TrilinearForm V) (hc : ∀ x y z, β x y z = β y z x) (x y z : V) :
    γ (dualProduct γ hγ β x y) z = γ x (dualProduct γ hγ β y z) := by
  rw [hs x, gamma_dualProduct, gamma_dualProduct, hc]

/-- Inside the isometry group, preserving the cubic form is equivalent to
preserving the product recovered by duality. -/
theorem preserves_beta_iff_product (γ : LinearMap.BilinForm ℝ V)
    (hγ : γ.Nondegenerate) (β : TrilinearForm V) (f : V ≃ₗ[ℝ] V)
    (hf : ∀ x y, γ (f x) (f y) = γ x y) :
    (∀ x y z, β (f x) (f y) (f z) = β x y z) ↔
      ∀ x y, dualProduct γ hγ β (f x) (f y) = f (dualProduct γ hγ β x y) := by
  constructor
  · intro h x y
    apply (γ.toDual hγ).injective
    ext z
    obtain ⟨w, rfl⟩ := f.surjective z
    change γ (dualProduct γ hγ β (f x) (f y)) (f w) =
      γ (f (dualProduct γ hγ β x y)) (f w)
    rw [gamma_dualProduct, hf, gamma_dualProduct, h]
  · intro h x y z
    rw [← gamma_dualProduct γ hγ β (f x) (f y) (f z), h, hf, gamma_dualProduct]

/-- The simultaneous stabilizer of two supplied forms. The final Griess carrier
must instantiate these forms on the fixed source space. -/
def formStabilizer (γ : LinearMap.BilinForm ℝ V) (β : TrilinearForm V) :
    Subgroup (V ≃ₗ[ℝ] V) where
  carrier f := (∀ x y, γ (f x) (f y) = γ x y) ∧
    (∀ x y z, β (f x) (f y) (f z) = β x y z)
  one_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x y
      exact (hf.1 (g x) (g y)).trans (hg.1 x y)
    · intro x y z
      exact (hf.2 (g x) (g y) (g z)).trans (hg.2 x y z)
  inv_mem' := by
    intro f hf
    constructor
    · intro x y
      have h := hf.1 (f.symm x) (f.symm y)
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using h.symm
    · intro x y z
      have h := hf.2 (f.symm x) (f.symm y) (f.symm z)
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using h.symm

/-- The same subgroup, characterized by the recovered algebra structure. -/
theorem mem_formStabilizer_iff (γ : LinearMap.BilinForm ℝ V)
    (hγ : γ.Nondegenerate) (β : TrilinearForm V) (f : V ≃ₗ[ℝ] V) :
    f ∈ formStabilizer γ β ↔
      (∀ x y, γ (f x) (f y) = γ x y) ∧
      (∀ x y, dualProduct γ hγ β (f x) (f y) = f (dualProduct γ hγ β x y)) := by
  constructor
  · intro h
    exact ⟨h.1, (preserves_beta_iff_product γ hγ β f h.1).mp h.2⟩
  · intro h
    exact ⟨h.1, (preserves_beta_iff_product γ hγ β f h.1).mpr h.2⟩

/-- Isometries preserving a specified bilinear multiplication. -/
def productStabilizer (γ : LinearMap.BilinForm ℝ V) (m : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    Subgroup (V ≃ₗ[ℝ] V) where
  carrier f := (∀ x y, γ (f x) (f y) = γ x y) ∧
    (∀ x y, m (f x) (f y) = f (m x y))
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x y
      exact (hf.1 (g x) (g y)).trans (hg.1 x y)
    · intro x y
      exact (hf.2 (g x) (g y)).trans (congrArg f (hg.2 x y))
  inv_mem' := by
    intro f hf
    constructor
    · intro x y
      have h := hf.1 (f.symm x) (f.symm y)
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using h.symm
    · intro x y
      apply f.injective
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using
        (hf.2 (f.symm x) (f.symm y)).symm

/-- The equality of stabilizers in Aschbacher 9.4(3), used in 28.12. -/
theorem formStabilizer_eq_productStabilizer (γ : LinearMap.BilinForm ℝ V)
    (hγ : γ.Nondegenerate) (β : TrilinearForm V) :
    formStabilizer γ β = productStabilizer γ (dualProduct γ hγ β) := by
  ext f
  exact mem_formStabilizer_iff γ hγ β f

end Sporadic.Monster.Construction.Griess
