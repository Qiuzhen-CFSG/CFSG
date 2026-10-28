/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/SymmetricMatrixSpace.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Data.Sym.Card

/-!
# SymmetricMatrixSpace

Symmetric matrices are coordinatized by unordered pairs. This linear equivalence
computes their dimension and provides genuine rank-one symmetric squares.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/SymmetricMatrixSpace.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries, public imports, and exposed concrete
definitions used by the downstream metric calculations.
-/

public section

noncomputable section
namespace Atlas.Algebra

/-- The actual linear subspace of symmetric matrices. -/
@[expose] def symmetricMatrixSpace (K I : Type*) [CommRing K] : Submodule K (Matrix I I K) where
  carrier := {M | ∀ i j, M i j=M j i}
  zero_mem' := by
    change ∀ i j, (0 : Matrix I I K) i j=(0 : Matrix I I K) j i
    intros; rfl
  add_mem' := by
    intro M N hM hN i j
    change M i j+N i j=M j i+N j i
    rw [hM i j,hN i j]
  smul_mem' a M hM := by intro i j; change a*_ = a*_; rw [hM i j]

theorem mem_symmetricMatrixSpace_iff {K I : Type*} [CommRing K] (M : Matrix I I K) :
    M ∈ symmetricMatrixSpace K I ↔ M.IsSymm := by
  constructor
  · intro h
    ext i j
    exact h j i
  · intro h i j
    exact congrFun (congrFun h j) i

/-- Unordered-pair coordinates are coordinates on the actual symmetric-matrix
vector space, not a replacement of the vector space by a finite multiset type. -/
@[expose] def symmetricMatrixCoordinates (K I : Type*) [CommRing K] :
    symmetricMatrixSpace K I ≃ₗ[K] (Sym2 I → K) where
  toFun M := Sym2.lift ⟨M.val,M.property⟩
  invFun f := ⟨fun i j => f (Sym2.mk i j),by intro i j; exact congrArg f Sym2.eq_swap⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv f := by funext s; induction s using Sym2.ind with | _ i j => rfl
  map_add' M N := by funext s; induction s using Sym2.ind with | _ i j => rfl
  map_smul' a M := by funext s; induction s using Sym2.ind with | _ i j => rfl

instance symmetricMatrixSpace_finite (K I : Type*) [Field K] [Fintype I] :
    Module.Finite K (symmetricMatrixSpace K I) :=
  Module.Finite.of_injective (symmetricMatrixCoordinates K I).toLinearMap
    (symmetricMatrixCoordinates K I).injective

theorem symmetricMatrixSpace_finrank (K I : Type*) [Field K] [Fintype I] :
    Module.finrank K (symmetricMatrixSpace K I)=(Fintype.card I+1).choose 2 := by
  rw [(symmetricMatrixCoordinates K I).finrank_eq,Module.finrank_fintype_fun_eq_card,Sym2.card]

theorem symmetricMatrixSpace_finrank_fin (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K (symmetricMatrixSpace K (Fin m))=m*(m+1)/2 := by
  rw [symmetricMatrixSpace_finrank,Fintype.card_fin,Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- The genuine rank-one symmetric matrix vvᵀ. -/
@[expose] def symmetricMatrixSquare {K I : Type*} [CommRing K] (v : I → K) :
    symmetricMatrixSpace K I :=
  ⟨fun i j => v i*v j,by intro i j; exact mul_comm _ _⟩

theorem symmetricMatrixSquare_apply {K I : Type*} [CommRing K] (v : I → K) (i j : I) :
    (symmetricMatrixSquare v).val i j=v i*v j := rfl

end Atlas.Algebra
