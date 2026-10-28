module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearAlgebra/DotProductFiber.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearAlgebra.LinearFunctionalFiber
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Affine fibres and projective scalar coordinates used to count singular vectors and points. -/

@[expose] public section

/-! # Fibres of the coordinate dot product over finite fields -/
noncomputable section
namespace Atlas.DotProduct
variable {n : ℕ} {F : Type*} [Field F]

def functional (x : Fin n → F) : (Fin n → F) →ₗ[F] F :=
  ∑ i : Fin n, x i • LinearMap.proj i

@[simp] theorem functional_apply (x y : Fin n → F) :
    functional x y = ∑ i : Fin n, x i * y i := by
  simp [functional,LinearMap.sum_apply]

theorem exists_normalized (x : Fin n → F) (hx : x ≠ 0) :
    ∃ y, functional x y = 1 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  refine ⟨Pi.single i (x i)⁻¹, ?_⟩
  simp [functional_apply,Pi.single_apply,hi]

theorem card_fiber [Finite F] (x : Fin n → F) (hx : x ≠ 0) (a : F) :
    Nat.card {y : Fin n → F // functional x y = a} = Nat.card F ^ (n-1) := by
  obtain ⟨y,hy⟩ := exists_normalized x hx
  simpa using Atlas.LinearFunctional.card_fiber (functional x) y hy a

/-- The exceptional zero functional has its entire domain as zero fibre. -/
def zeroFiberEquiv : {y : Fin n → F // functional (0 : Fin n → F) y=0} ≃ (Fin n → F) where
  toFun y := y.val
  invFun y := ⟨y,by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_zeroFiber [Finite F] :
    Nat.card {y : Fin n → F // functional (0 : Fin n → F) y=0} = Nat.card F ^ n := by
  rw [Nat.card_congr zeroFiberEquiv, Nat.card_fun, Nat.card_fin]

end Atlas.DotProduct
