module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearAlgebra/LinearFunctionalFiber.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Affine fibres and projective scalar coordinates used to count singular vectors and points. -/

@[expose] public section

noncomputable section
namespace Atlas.LinearFunctional
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Translation by a normalized section identifies each affine fibre with the kernel. -/
def fiberEquivKernel (l : V →ₗ[F] F) (v : V) (hv : l v = 1) (c : F) :
    {x : V // l x = c} ≃ l.ker where
  toFun x := ⟨x.val-c • v, by simp [map_sub,map_smul,x.prop,hv]⟩
  invFun x := ⟨x.val+c • v, by simp [map_add,map_smul,hv]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem card_fiber [Finite F] [FiniteDimensional F V]
    (l : V →ₗ[F] F) (v : V) (hv : l v = 1) (c : F) :
    Nat.card {x : V // l x = c} = Nat.card F ^ (Module.finrank F V - 1) := by
  have hr : LinearMap.range l = ⊤ := LinearMap.range_eq_top.mpr (by
    intro a
    exact ⟨a • v,by simp [map_smul,hv]⟩)
  have hk := l.finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self] at hk
  have hd : Module.finrank F l.ker = Module.finrank F V - 1 := by omega
  rw [Nat.card_congr (fiberEquivKernel l v hv c),Module.natCard_eq_pow_finrank (K := F),hd]
end Atlas.LinearFunctional
