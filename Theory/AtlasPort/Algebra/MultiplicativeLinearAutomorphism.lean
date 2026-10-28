module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/Algebra/MultiplicativeLinearAutomorphism.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
set_option warningAsError false

@[expose] public section

/-! Multiplication-preserving linear automorphisms without associativity assumptions. -/
namespace Atlas.Algebra
variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The full subgroup preserving a specified multiplication; no associativity is required. -/
def multiplicativeLinearAut (m : V → V → V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ x y, g (m x y) = m (g x) (g y)}
  one_mem' := by change ∀ x y, m x y = m x y; intros; rfl
  mul_mem' {g h} hg hh := by
    intro x y
    change g (h (m x y)) = m (g (h x)) (g (h y))
    rw [hh, hg]
  inv_mem' {g} hg := by
    intro x y
    apply g.injective
    change g (g.symm (m x y)) = g (m (g.symm x) (g.symm y))
    rw [g.apply_symm_apply, hg, g.apply_symm_apply, g.apply_symm_apply]

namespace MultiplicativeLinearAut
variable {m : V → V → V}

def toLinearEquiv (g : multiplicativeLinearAut (R := R) m) : V ≃ₗ[R] V := g.val

@[simp] theorem map_mul (g : multiplicativeLinearAut (R := R) m) (x y : V) :
    toLinearEquiv g (m x y) = m (toLinearEquiv g x) (toLinearEquiv g y) := g.property x y

/-- Surjectivity forces preservation of a two-sided identity. -/
theorem map_unit (g : multiplicativeLinearAut (R := R) m) (u : V)
    (hleft : ∀ x, m u x = x) (hright : ∀ x, m x u = x) :
    toLinearEquiv g u = u := by
  obtain ⟨x, hx⟩ := g.val.surjective u
  have h := g.property u x
  rw [hleft, hx, hright] at h
  exact h.symm

@[ext] theorem ext {g h : multiplicativeLinearAut (R := R) m}
    (he : ∀ x, toLinearEquiv g x = toLinearEquiv h x) : g = h :=
  Subtype.ext (LinearEquiv.ext he)
instance faithfulAction : FaithfulSMul (multiplicativeLinearAut (R := R) m) V where
  eq_of_smul_eq_smul h := ext h

/-- The inclusion is the faithful linear representation. -/
def representation : multiplicativeLinearAut (R := R) m →* (V ≃ₗ[R] V) :=
  (multiplicativeLinearAut (R := R) m).subtype

theorem representation_injective : Function.Injective
    (representation (R := R) (m := m)) := Subtype.val_injective

end MultiplicativeLinearAut
end Atlas.Algebra
