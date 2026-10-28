/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianRightIdeals.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoKernel
public import Mathlib.Algebra.Module.Opposite

/-!
# IcosianRightIdeals

Preimages of matrices with one specified zero row are right ideals
of the integral order. Matrix multiplication proves closure; their
intersection is twice the order, and surjectivity distinguishes them.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianRightIdeals.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix

/-- The preimage of the matrices having a specified row zero, a right ideal. -/
def icosianRowRightIdeal (r : Fin 2) : Submodule icosianOrderᵐᵒᵖ icosianOrder where
  carrier := {x | ∀ j, icosianModuloTwo x r j=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j; simp [map_add,hx j,hy j]
  smul_mem' := by
    intro a x hx j
    change ∀ j, icosianModuloTwo x r j=0 at hx
    change icosianModuloTwo (x*MulOpposite.unop a) r j=0
    rw [map_mul]
    simp [Matrix.mul_apply,hx]

/-- P consists of the matrices with second row zero (columns in the first coordinate line). -/
def icosianP : Submodule icosianOrderᵐᵒᵖ icosianOrder := icosianRowRightIdeal 1

/-- P₀ consists of the matrices with first row zero (columns in the second coordinate line). -/
def icosianPZero : Submodule icosianOrderᵐᵒᵖ icosianOrder := icosianRowRightIdeal 0

theorem icosianP_mem (x : icosianOrder) : x ∈ icosianP ↔ ∀ j,icosianModuloTwo x 1 j=0 := Iff.rfl

theorem icosianPZero_mem (x : icosianOrder) : x ∈ icosianPZero ↔ ∀ j,icosianModuloTwo x 0 j=0 := Iff.rfl

theorem icosianP_intersection (x : icosianOrder) :
    x ∈ icosianP ⊓ icosianPZero ↔ ∃ y : icosianOrder,x=2*y := by
  rw [← icosianModuloTwo_eq_zero_iff_two_mul]
  constructor
  · rintro ⟨h1,h0⟩
    funext i j
    fin_cases i
    · exact h0 j
    · exact h1 j
  · intro h
    constructor <;> intro j <;> rw [h] <;> rfl

theorem icosianP_ne_PZero : icosianP≠icosianPZero := by
  obtain ⟨x,hx⟩ := icosianModuloTwo_surjective (!![1,0;0,0] : IcosianMatrix)
  have hp : x ∈ icosianP := by intro j; rw [hx]; fin_cases j <;> rfl
  have hn : x ∉ icosianPZero := by
    intro h
    have he := h 0
    rw [hx] at he
    exact one_ne_zero he
  intro h
  exact hn (h ▸ hp)

end Atlas.Algebra
