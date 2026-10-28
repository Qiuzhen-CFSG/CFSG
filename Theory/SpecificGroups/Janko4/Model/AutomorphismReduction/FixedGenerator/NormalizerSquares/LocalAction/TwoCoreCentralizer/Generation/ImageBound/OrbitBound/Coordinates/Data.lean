module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates.Tables
/-!
# Exact column certificates for the twelve-dimensional homology splitting

The matrices N, S, Q, T satisfy N = a - 1, NS = 0, QN = 0, QS = 1,
and NT + TN + SQ = 1. Thus the section and projection are inverse on
ker(N)/im(N). The final certificates compute QxS and QyS for the actual
conjugated ATLAS generators. Tables are witnesses only; every identity is
checked in Lean's kernel. See Tables.lean and ImageBound/source/README.md
for the original ATLAS attribution and column convention.
-/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
set_option maxRecDepth 10000

def N : BinaryMatrix := columns nCols
def S : Matrix (Fin 112) (Fin 12) (ZMod 2) := columns sectionCols
def Q : Matrix (Fin 12) (Fin 112) (ZMod 2) := columns quotientCols
def T : BinaryMatrix := columns homotopyCols
def actionCols (b : Bool) : Fin 12 → ℕ := if b then qyCols else qxCols
def actionMatrix (b : Bool) : Matrix (Fin 12) (Fin 12) (ZMod 2) := columns (actionCols b)
def generatorCols (b : Bool) : Fin 112 → ℕ := if b then yCols else xCols
def generatorMatrix (b : Bool) : BinaryMatrix := columns (generatorCols b)
def generator (b : Bool) : localSubgroup := if b then subgroupY else subgroupX

set_option maxHeartbeats 4000000 in
theorem N_eq : N = matrixA - 1 := by
  let : ∀ i j : Fin 112, Decidable (N i j = (matrixA - 1) i j) := fun _ _ => inferInstance
  exact funext (fun i => funext (allFin₂ (fun i j => N i j = (matrixA - 1) i j)
    (by decide +kernel) i))

set_option maxHeartbeats 4000000 in
theorem generatorMatrix_eq (b : Bool) :
    generatorMatrix b = ((generator b : BinaryMatrixˣ) : BinaryMatrix) := by
  cases b
  · change (columns xCols : BinaryMatrix) = toMatrix cx
    rw [eval_cx]
    let : ∀ i j : Fin 112, Decidable ((columns xCols : BinaryMatrix) i j = decodeRows cxRows i j) := fun _ _ => inferInstance
    exact funext (fun i => funext (allFin₂ (fun i j =>
      (columns xCols : BinaryMatrix) i j = decodeRows cxRows i j) (by decide +kernel) i))
  · change (columns yCols : BinaryMatrix) = toMatrix cy
    rw [eval_cy]
    let : ∀ i j : Fin 112, Decidable ((columns yCols : BinaryMatrix) i j = decodeRows cyRows i j) := fun _ _ => inferInstance
    exact funext (fun i => funext (allFin₂ (fun i j =>
      (columns yCols : BinaryMatrix) i j = decodeRows cyRows i j) (by decide +kernel) i))

theorem columns_zero {m n : ℕ} :
    (columns (fun _ : Fin n => 0) : Matrix (Fin m) (Fin n) (ZMod 2)) = 0 := by
  ext i j
  simp [columns, bit]

set_option maxHeartbeats 4000000 in
theorem N_S : N * S = 0 := by
  rw [N, S, columns_mul]
  rw [← columns_zero (m := 112) (n := 12)]
  congr 1
  exact funext (allFin _ (by decide +kernel))

set_option maxHeartbeats 4000000 in
theorem Q_N : Q * N = 0 := by
  rw [Q, N, columns_mul]
  rw [← columns_zero (m := 12) (n := 112)]
  congr 1
  exact funext (allFin _ (by decide +kernel))

set_option maxHeartbeats 4000000 in
theorem Q_S : Q * S = 1 := by
  rw [Q, S, columns_mul, ← columns_one 12]
  congr 1
  exact funext (allFin _ (by decide +kernel))

set_option maxHeartbeats 4000000 in
/-- A contraction of the literal displacement, with the twelve section columns. -/
theorem contraction : N * T + T * N + S * Q = 1 := by
  rw [N, T, S, Q, columns_mul, columns_mul, columns_mul,
    ← columns_xor, ← columns_xor, ← columns_one 112]
  congr 1
  exact funext (allFin _ (by decide +kernel))

set_option maxHeartbeats 4000000 in
theorem Q_generator_S (b : Bool) : Q * (generatorMatrix b * S) = actionMatrix b := by
  cases b <;> simp only [Q, generatorMatrix, generatorCols, S, actionMatrix, actionCols,
    Bool.false_eq_true, ↓reduceIte, columns_mul] <;>
    congr 1 <;> exact funext (allFin _ (by decide +kernel))

set_option maxHeartbeats 4000000 in
theorem S_seed : S *ᵥ vectorOfCode 14 = distinguishedVector := by
  change columns sectionCols *ᵥ decode 14 = distinguishedVector
  rw [← decode_combine]
  have h : combine sectionCols 14 = 15988596176158495 := by decide +kernel
  rw [h]
  rfl
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Coordinates
