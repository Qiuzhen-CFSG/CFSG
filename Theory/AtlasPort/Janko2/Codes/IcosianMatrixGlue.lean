/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianMatrixGlue.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianGlueDimension
public import Theory.AtlasPort.Janko2.Codes.IcosianGlueMonomial

/-!
# IcosianMatrixGlue

The matrix version of the glue consists of two glue columns. An explicit
linear equivalence proves dimension six and cardinality 4096 over four
elements; column formulas prove closure under right matrix multiplication.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianMatrixGlue.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix

abbrev IcosianMatrixGlueWord (F : Type*) := Fin 3 → Matrix (Fin 2) (Fin 2) F

def icosianGlueColumn {F : Type*} (x : IcosianMatrixGlueWord F) (j : Fin 2) :
    IcosianGlueWord F := fun i r => x i r j

/-- The actual right-matrix glue corresponding to the Morita image W. Both
columns must lie in W; its scalar dimension is six, rather than three. -/
def icosianMatrixGlue (F : Type*) [Field F] :
    Submodule F (IcosianMatrixGlueWord F) where
  carrier := {x | ∀ j : Fin 2,icosianGlueColumn x j ∈ icosianGlue F}
  zero_mem' := fun _ => (icosianGlue F).zero_mem
  add_mem' := by
    intro x y hx hy j
    exact (icosianGlue F).add_mem (hx j) (hy j)
  smul_mem' := fun a _ hx j => (icosianGlue F).smul_mem a (hx j)

@[simp] theorem mem_icosianMatrixGlue {F : Type*} [Field F]
    (x : IcosianMatrixGlueWord F) :
    x ∈ icosianMatrixGlue F ↔ ∀ j : Fin 2,icosianGlueColumn x j ∈ icosianGlue F := Iff.rfl

/-- Complete coefficient constraints, with no omitted column condition. -/
theorem icosianMatrixGlue_constraints {F : Type*} [Field F]
    (x : IcosianMatrixGlueWord F) : x ∈ icosianMatrixGlue F ↔
    ∀ j : Fin 2,x 0 1 j=x 1 1 j ∧ x 1 1 j=x 2 1 j ∧
      x 0 0 j+x 1 0 j+x 2 0 j=0 := Iff.rfl

def icosianMatrixGlueEncoder {F : Type*} (u v : IcosianGlueWord F) :
    IcosianMatrixGlueWord F := fun i r j => ![u i r,v i r] j

@[simp] theorem icosianMatrixGlueEncoder_column_zero {F : Type*}
    (u v : IcosianGlueWord F) : icosianGlueColumn (icosianMatrixGlueEncoder u v) 0=u := rfl

@[simp] theorem icosianMatrixGlueEncoder_column_one {F : Type*}
    (u v : IcosianGlueWord F) : icosianGlueColumn (icosianMatrixGlueEncoder u v) 1=v := rfl

theorem icosianMatrixGlue_reconstruct {F : Type*} (x : IcosianMatrixGlueWord F) :
    icosianMatrixGlueEncoder (icosianGlueColumn x 0) (icosianGlueColumn x 1)=x := by
  funext i r j
  fin_cases j <;> rfl

theorem icosianMatrixGlueEncoder_mem {F : Type*} [Field F]
    (u v : icosianGlue F) : icosianMatrixGlueEncoder u.val v.val ∈ icosianMatrixGlue F := by
  intro j
  fin_cases j
  · exact u.property
  · exact v.property

/-- Explicit scalar-linear reconstruction from the two Morita columns. -/
def icosianMatrixGlueLinearEquiv (F : Type*) [Field F] :
    (icosianGlue F × icosianGlue F) ≃ₗ[F] icosianMatrixGlue F where
  toFun p := ⟨icosianMatrixGlueEncoder p.1.val p.2.val,icosianMatrixGlueEncoder_mem _ _⟩
  invFun x := (⟨icosianGlueColumn x.val 0,x.property 0⟩,
    ⟨icosianGlueColumn x.val 1,x.property 1⟩)
  left_inv p := rfl
  right_inv x := Subtype.ext (icosianMatrixGlue_reconstruct x.val)
  map_add' p q := by
    apply Subtype.ext
    funext i r j
    fin_cases j <;> rfl
  map_smul' a p := by
    apply Subtype.ext
    funext i r j
    fin_cases j <;> rfl

theorem icosianMatrixGlue_finrank {F : Type*} [Field F] :
    Module.finrank F (icosianMatrixGlue F)=6 := by
  rw [← (icosianMatrixGlueLinearEquiv F).finrank_eq,Module.finrank_prod,
    icosianGlue_finrank]

theorem icosianMatrixGlue_card {F : Type*} [Field F] [Finite F] :
    Nat.card (icosianMatrixGlue F)=Nat.card F^6 := by
  rw [← Nat.card_congr (icosianMatrixGlueLinearEquiv F).toEquiv,Nat.card_prod,
    icosianGlue_card]
  ring

theorem icosianMatrixGlue_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=4) : Nat.card (icosianMatrixGlue F)=4096 := by
  rw [icosianMatrixGlue_card,hF]
  norm_num

def icosianMatrixGlueRightMul {F : Type*} [Field F]
    (x : IcosianMatrixGlueWord F) (a : Matrix (Fin 2) (Fin 2) F) :
    IcosianMatrixGlueWord F := fun i => x i*a

theorem icosianMatrixGlueRightMul_column {F : Type*} [Field F]
    (x : IcosianMatrixGlueWord F) (a : Matrix (Fin 2) (Fin 2) F) (j : Fin 2) :
    icosianGlueColumn (icosianMatrixGlueRightMul x a) j=
      a 0 j • icosianGlueColumn x 0+a 1 j • icosianGlueColumn x 1 := by
  funext i r
  simp [icosianGlueColumn,icosianMatrixGlueRightMul,Matrix.mul_apply,
    Fin.sum_univ_two,smul_eq_mul,mul_comm]

/-- Stability under every right2-by-2 matrix, not just scalar units. -/
theorem icosianMatrixGlue_right_mem {F : Type*} [Field F]
    (x : IcosianMatrixGlueWord F) (hx : x ∈ icosianMatrixGlue F)
    (a : Matrix (Fin 2) (Fin 2) F) :
    icosianMatrixGlueRightMul x a ∈ icosianMatrixGlue F := by
  intro j
  rw [icosianMatrixGlueRightMul_column]
  exact (icosianGlue F).add_mem ((icosianGlue F).smul_mem _ (hx 0))
    ((icosianGlue F).smul_mem _ (hx 1))

end Atlas.Codes
