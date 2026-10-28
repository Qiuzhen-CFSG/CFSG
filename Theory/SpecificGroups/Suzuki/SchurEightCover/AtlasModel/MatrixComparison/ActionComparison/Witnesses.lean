module
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockModel
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Pair
/-!
# Checked row-line witnesses for the Suzuki action comparison

The rows and the block-to-point bijection are the literal numerical data in
`AtlasModel/source/ovoid.json`. The kernel checks that the rows are distinct,
that the label maps are inverse, and that the two published block permutations
and matrices preserve the same row lines. The relation uses
`row (p i) * g = c • row i`: this reverses the saved right action exactly as
required for Lean's permutation multiplication, while retaining ordinary
matrix multiplication.

The five displayed rows are used by `Faithfulness.lean` to exclude a projective
kernel. The determinant and fourth-root checks then exclude nontrivial scalars.
Source context: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407.
Numerical provenance and attribution: `AtlasModel/source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison
open Matrix
def pointRow (i : Fin 65) : Fin 4 → F8 :=
  match i with
  | ⟨n, _⟩ => (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then ![code 1, code 0, code 0, code 0] else ![code 1, code 1, code 0, code 1]) else (if n < 3 then ![code 0, code 0, code 0, code 1] else ![code 1, code 0, code 1, code 1])) else (if n < 6 then (if n < 5 then ![code 1, code 7, code 0, code 2] else ![code 1, code 1, code 1, code 1]) else (if n < 7 then ![code 1, code 0, code 3, code 2] else ![code 1, code 3, code 7, code 5]))) else (if n < 12 then (if n < 10 then (if n < 9 then ![code 1, code 6, code 0, code 3] else ![code 1, code 0, code 6, code 7]) else (if n < 11 then ![code 1, code 7, code 3, code 2] else ![code 1, code 1, code 3, code 6])) else (if n < 14 then (if n < 13 then ![code 1, code 0, code 5, code 3] else ![code 1, code 2, code 0, code 7]) else (if n < 15 then ![code 1, code 7, code 1, code 5] else ![code 1, code 2, code 2, code 6])))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then ![code 1, code 3, code 6, code 4] else ![code 1, code 5, code 6, code 2]) else (if n < 19 then ![code 1, code 5, code 0, code 4] else ![code 1, code 0, code 4, code 6])) else (if n < 22 then (if n < 21 then ![code 1, code 1, code 6, code 4] else ![code 1, code 3, code 1, code 2]) else (if n < 23 then ![code 1, code 6, code 5, code 3] else ![code 1, code 2, code 6, code 7]))) else (if n < 28 then (if n < 26 then (if n < 25 then ![code 1, code 0, code 7, code 4] else ![code 1, code 7, code 5, code 7]) else (if n < 27 then ![code 1, code 5, code 3, code 3] else ![code 1, code 1, code 5, code 4])) else (if n < 30 then (if n < 29 then ![code 1, code 3, code 0, code 6] else ![code 1, code 4, code 2, code 5]) else (if n < 31 then ![code 1, code 3, code 3, code 4] else ![code 1, code 6, code 3, code 6]))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then ![code 1, code 4, code 3, code 4] else ![code 1, code 4, code 0, code 5]) else (if n < 35 then ![code 1, code 1, code 4, code 7] else ![code 1, code 4, code 4, code 3])) else (if n < 38 then (if n < 37 then ![code 1, code 7, code 4, code 1] else ![code 1, code 2, code 1, code 5]) else (if n < 39 then ![code 1, code 6, code 1, code 2] else ![code 1, code 4, code 1, code 3]))) else (if n < 44 then (if n < 42 then (if n < 41 then ![code 1, code 5, code 4, code 7] else ![code 1, code 0, code 2, code 5]) else (if n < 43 then ![code 1, code 3, code 5, code 5] else ![code 1, code 7, code 7, code 5])) else (if n < 46 then (if n < 45 then ![code 1, code 2, code 3, code 3] else ![code 1, code 7, code 2, code 7]) else (if n < 47 then ![code 1, code 5, code 1, code 3] else ![code 1, code 5, code 7, code 4])))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then ![code 1, code 3, code 4, code 6] else ![code 1, code 4, code 7, code 1]) else (if n < 51 then ![code 1, code 1, code 7, code 6] else ![code 1, code 6, code 7, code 1])) else (if n < 54 then (if n < 53 then ![code 1, code 6, code 2, code 6] else ![code 1, code 4, code 5, code 4]) else (if n < 55 then ![code 1, code 2, code 5, code 5] else ![code 1, code 5, code 5, code 7]))) else (if n < 60 then (if n < 58 then (if n < 57 then ![code 1, code 2, code 4, code 3] else ![code 1, code 7, code 6, code 1]) else (if n < 59 then ![code 1, code 5, code 2, code 2] else ![code 1, code 6, code 6, code 2])) else (if n < 62 then (if n < 61 then ![code 1, code 4, code 6, code 1] else ![code 1, code 1, code 2, code 7]) else (if n < 63 then ![code 1, code 2, code 7, code 6] else (if n < 64 then ![code 1, code 6, code 4, code 1] else ![code 1, code 3, code 2, code 2])))))))

def blockToPoint (i : Fin 65) : Fin 65 :=
  match i with
  | ⟨n, _⟩ => (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 23 else 18) else (if n < 3 then 12 else 45)) else (if n < 6 then (if n < 5 then 33 else 43) else (if n < 7 then 17 else 55))) else (if n < 12 then (if n < 10 then (if n < 9 then 41 else 51) else (if n < 11 then 13 else 3)) else (if n < 14 then (if n < 13 then 53 else 25) else (if n < 15 then 63 else 28)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 58 else 47) else (if n < 19 then 39 else 46)) else (if n < 22 then (if n < 21 then 62 else 60) else (if n < 23 then 32 else 64))) else (if n < 28 then (if n < 26 then (if n < 25 then 27 else 2) else (if n < 27 then 52 else 24)) else (if n < 30 then (if n < 29 then 40 else 49) else (if n < 31 then 11 else 8))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 38 else 31) else (if n < 35 then 54 else 44)) else (if n < 38 then (if n < 37 then 61 else 56) else (if n < 39 then 20 else 15))) else (if n < 44 then (if n < 42 then (if n < 41 then 10 else 21) else (if n < 43 then 14 else 37)) else (if n < 46 then (if n < 45 then 35 else 7) else (if n < 47 then 16 else 48)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 30 else 1) else (if n < 51 then 9 else 22)) else (if n < 54 then (if n < 53 then 4 else 59) else (if n < 55 then 42 else 36))) else (if n < 60 then (if n < 58 then (if n < 57 then 26 else 19) else (if n < 59 then 34 else 5)) else (if n < 62 then (if n < 61 then 6 else 57) else (if n < 63 then 0 else (if n < 64 then 50 else 29)))))))

def pointToBlock (i : Fin 65) : Fin 65 :=
  match i with
  | ⟨n, _⟩ => (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 62 else 49) else (if n < 3 then 25 else 11)) else (if n < 6 then (if n < 5 then 52 else 59) else (if n < 7 then 60 else 45))) else (if n < 12 then (if n < 10 then (if n < 9 then 31 else 50) else (if n < 11 then 40 else 30)) else (if n < 14 then (if n < 13 then 2 else 10) else (if n < 15 then 42 else 39)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 46 else 6) else (if n < 19 then 1 else 57)) else (if n < 22 then (if n < 21 then 38 else 41) else (if n < 23 then 51 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 27 else 13) else (if n < 27 then 56 else 24)) else (if n < 30 then (if n < 29 then 15 else 64) else (if n < 31 then 48 else 33))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 22 else 4) else (if n < 35 then 58 else 44)) else (if n < 38 then (if n < 37 then 55 else 43) else (if n < 39 then 32 else 18))) else (if n < 44 then (if n < 42 then (if n < 41 then 28 else 8) else (if n < 43 then 54 else 5)) else (if n < 46 then (if n < 45 then 35 else 3) else (if n < 47 then 19 else 17)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 47 else 29) else (if n < 51 then 63 else 9)) else (if n < 54 then (if n < 53 then 26 else 12) else (if n < 55 then 34 else 7))) else (if n < 60 then (if n < 58 then (if n < 57 then 37 else 61) else (if n < 59 then 16 else 53)) else (if n < 62 then (if n < 61 then 21 else 36) else (if n < 63 then 20 else (if n < 64 then 14 else 23)))))))

def pointEquiv : Fin 65 ≃ Fin 65 where
  toFun := blockToPoint
  invFun := pointToBlock
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row (i : Fin 65) : Fin 4 → F8 := pointRow (pointEquiv i)

theorem pointRow_injective : Function.Injective pointRow := by decide +kernel

theorem pointRow_first : ∀ i : Fin 65, i ≠ 2 → pointRow i 0 = 1 := by decide +kernel

theorem pointRow_two : pointRow 2 = ![0,0,0,1] := by decide +kernel

theorem row_frame :
    row 62 = ![1,0,0,0] ∧ row 49 = ![1,1,0,1] ∧
    row 25 = ![0,0,0,1] ∧ row 11 = ![1,0,1,1] ∧
    row 59 = ![1,1,1,1] := by decide +kernel

theorem generatorA_rows : ∀ i : Fin 65, ∃ c : F8, c ≠ 0 ∧
    row (BlockModel.a i) ᵥ* (matrixA : Mat) = c • row i := by decide +kernel

theorem generatorB_rows : ∀ i : Fin 65, ∃ c : F8, c ≠ 0 ∧
    row (BlockModel.b i) ᵥ* (matrixB : Mat) = c • row i := by decide +kernel

theorem matrixA_det : (matrixA : Mat).det = 1 := by decide +kernel

theorem matrixB_det : (matrixB : Mat).det = 1 := by decide +kernel

theorem fourth_root_one : ∀ c : F8, c ^ 4 = 1 → c = 1 := by decide +kernel
end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison
