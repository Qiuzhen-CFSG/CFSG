module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Determinant

/-!
# Classical isometry point groups

This module defines the abstract point groups used by the concrete orthogonal
and symplectic algebraic-group carriers.  A quadratic or bilinear isometry is a
linear equivalence preserving the specified form; the special-orthogonal group
also imposes determinant one.  These definitions are independent of the
classification of semisimple groups and therefore belong below the numbered
type-classification theorems.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

public def quadraticIsometrySubgroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {f | ∀ v, Q (f v) = Q v}
  one_mem' := by intro v; rfl
  mul_mem' := by
    intro f g hf hg v
    rw [LinearEquiv.mul_apply, hf, hg]
  inv_mem' := by
    intro f hf v
    simpa using (hf (f⁻¹ v)).symm

/-- Membership in the quadratic-isometry point subgroup. -/
public lemma mem_quadraticIsometrySubgroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) (f : V ≃ₗ[k] V) :
    f ∈ quadraticIsometrySubgroup Q ↔ ∀ v, Q (f v) = Q v := by
  rfl

public noncomputable def specialOrthogonalPointGroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) : Subgroup (V ≃ₗ[k] V) :=
  quadraticIsometrySubgroup Q ⊓ LinearEquiv.det.ker

/-- Membership in the special-orthogonal point group is preservation of the
quadratic form together with determinant one. -/
public lemma mem_specialOrthogonalPointGroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) (f : V ≃ₗ[k] V) :
    f ∈ specialOrthogonalPointGroup Q ↔
      (∀ v, Q (f v) = Q v) ∧ LinearEquiv.det f = 1 := by
  rfl

public def bilinearIsometrySubgroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {f | ∀ v w, B (f v) (f w) = B v w}
  one_mem' := by intro v w; rfl
  mul_mem' := by
    intro f g hf hg v w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hf, hg]
  inv_mem' := by
    intro f hf v w
    simpa using (hf (f⁻¹ v) (f⁻¹ w)).symm

/-- Membership in the bilinear-isometry point subgroup is preservation of the
bilinear form. -/
public lemma mem_bilinearIsometrySubgroup
    {V : Type u} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (f : V ≃ₗ[k] V) :
    f ∈ bilinearIsometrySubgroup B ↔
      ∀ v w, B (f v) (f w) = B v w := by
  rfl

end Theory.AlgebraicGroup
