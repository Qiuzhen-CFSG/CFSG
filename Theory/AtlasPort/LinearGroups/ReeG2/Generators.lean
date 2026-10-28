module

/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/LinearGroups/ReeG2/Generators.lean at
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Changes: project module/public-import conventions; Lean 4.33 compatibility.
-/

public import Theory.AtlasPort.FieldTheory.ReeTitsAutomorphism
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Block

/-! The natural seven-dimensional small Ree matrices, in the job's upper-triangular
row-vector convention. Matrix multiplication is ordinary multiplication; a later
left action on points uses inverse matrices. All indices in source are zero-based. -/
@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Mat (F : Type*) := Matrix (Fin 7) (Fin 7) F
abbrev Ambient (F : Type*) [Field F] := Matrix.GeneralLinearGroup (Fin 7) F

def alphaMatrix (m : ℕ) (x : F) : Mat F :=
  let t := theta F m x
  !![1, t, 0, 0, -(t^3*x), -(t^3*x^2), t^4*x^2;
     0, 1, x, t*x, -(t^2*x), 0, -(t^3*x^2);
     0, 0, 1, t, -(t^2), 0, t^3*x;
     0, 0, 0, 1, t, 0, 0;
     0, 0, 0, 0, 1, -x, t*x;
     0, 0, 0, 0, 0, 1, -t;
     0, 0, 0, 0, 0, 0, 1]

theorem alpha_det (m : ℕ) (x : F) : (alphaMatrix m x).det = 1 := by
  have ht : (alphaMatrix m x).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [alphaMatrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [alphaMatrix, Fin.prod_univ_succ]

def alpha (m : ℕ) (x : F) : Ambient F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (alphaMatrix m x) (by rw [alpha_det]; exact one_ne_zero)

@[simp] theorem alpha_val (m : ℕ) (x : F) :
    (alpha m x).val = alphaMatrix m x := rfl

def betaMatrix (m : ℕ) (x : F) : Mat F :=
  let t := theta F m x
  !![1, 0, -t, 0, -x, 0, -(t*x);
     0, 1, 0, t, 0, -(t^2), 0;
     0, 0, 1, 0, 0, 0, x;
     0, 0, 0, 1, 0, t, 0;
     0, 0, 0, 0, 1, 0, t;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

theorem beta_det (m : ℕ) (x : F) : (betaMatrix m x).det = 1 := by
  have ht : (betaMatrix m x).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [betaMatrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [betaMatrix, Fin.prod_univ_succ]

def beta (m : ℕ) (x : F) : Ambient F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (betaMatrix m x) (by rw [beta_det]; exact one_ne_zero)

@[simp] theorem beta_val (m : ℕ) (x : F) :
    (beta m x).val = betaMatrix m x := rfl

def gammaMatrix (m : ℕ) (x : F) : Mat F :=
  let t := theta F m x
  !![1, 0, 0, -t, 0, -x, -(t^2);
     0, 1, 0, 0, -t, 0, x;
     0, 0, 1, 0, 0, t, 0;
     0, 0, 0, 1, 0, 0, -t;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

theorem gamma_det (m : ℕ) (x : F) : (gammaMatrix m x).det = 1 := by
  have ht : (gammaMatrix m x).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [gammaMatrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [gammaMatrix, Fin.prod_univ_succ]

def gamma (m : ℕ) (x : F) : Ambient F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (gammaMatrix m x) (by rw [gamma_det]; exact one_ne_zero)

@[simp] theorem gamma_val (m : ℕ) (x : F) :
    (gamma m x).val = gammaMatrix m x := rfl

def upsilonMatrix : Mat F :=
  !![0,0,0,0,0,0,-1;0,0,0,0,0,-1,0;0,0,0,0,-1,0,0;
     0,0,0,-1,0,0,0;0,0,-1,0,0,0,0;0,-1,0,0,0,0,0;-1,0,0,0,0,0,0]

omit [Finite F] [CharP F 3] in
theorem upsilonMatrix_square : upsilonMatrix (F := F) * upsilonMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [upsilonMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

def upsilon : Ambient F :=
  ⟨upsilonMatrix, upsilonMatrix, upsilonMatrix_square, upsilonMatrix_square⟩

omit [Finite F] [CharP F 3] in
@[simp] theorem upsilon_square : (upsilon : Ambient F) * upsilon = 1 := by
  apply Units.ext
  exact upsilonMatrix_square

/-- Diagonal matrix unit, keeping the inverse explicit. -/
def diagonalUnit (d : Fin 7 → Fˣ) : Ambient F where
  val := Matrix.diagonal (fun i => (d i : F))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : Fˣ))
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

def torusDiagonal (m : ℕ) (l : Fˣ) : Fin 7 → Fˣ :=
  let t := Units.map (theta F m).toMonoidHom l
  ![t, l/t, t^2/l, 1, l/t^2, t/l, t⁻¹]

def torus (m : ℕ) (l : Fˣ) : Ambient F := diagonalUnit (torusDiagonal m l)

theorem torus_mul (m : ℕ) (l k : Fˣ) : torus m (l*k) = torus m l * torus m k := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [torusDiagonal, div_eq_mul_inv, mul_pow, mul_comm, mul_left_comm, mul_assoc]

theorem torus_injective (m : ℕ) : Function.Injective (torus (F := F) m) := by
  intro l k h
  have h0 := congrArg (fun g : Ambient F => g.val 0 0) h
  change theta F m (l : F) = theta F m (k : F) at h0
  exact Units.ext ((theta F m).injective h0)

/-- The actual generated matrix subgroup; no target order or simplicity is assumed. -/
def generated (F : Type*) [Field F] [Finite F] [CharP F 3] (m : ℕ) : Subgroup (Ambient F) :=
  Subgroup.closure (Set.range (alpha (F := F) m) ∪ Set.range (beta (F := F) m) ∪
    Set.range (gamma (F := F) m) ∪ Set.range (torus (F := F) m) ∪ {upsilon})

abbrev Model (F : Type*) [Field F] [Finite F] [CharP F 3] (m : ℕ) := ↥(generated F m)

instance (m : ℕ) : Finite (Model F m) := inferInstance
end Atlas.ReeG2
