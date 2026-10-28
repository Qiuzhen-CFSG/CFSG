module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Algebra.CharP.Two

/-!
# Excluding reversed adjacent support in the natural–exterior tensor

The coordinates `(i,p)` represent `eᵢ ⊗ eₚ`, with the exterior pairs ordered
01, 02, 03, 12, 13, 23. The action is the literal Kronecker product of the
natural matrix and its second compound matrix. Its composition law follows
from the checked compound action, imported from the attributed ATLAS port.

The three simple upper roots, the root-0 exchange, and the active root-1
relation force all 24 coordinates to vanish. Thus this module contains no
nonzero local highest vector of support {1,2}. This is the concrete model
calculation for support separation; constructing the comparison from an
arbitrary irreducible module with support {0,1} is a separate obligation.

Source application: Guralnick–Malle, Classification of 2F-modules II,
author manuscript, Proposition 4.8(3), pp.27–28; Aschbacher–Smith K.3.2,
printed pp.454–455. The compound-matrix definitions and their attribution
are in `Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction`.
-/

@[expose] public section

open Representation
open Atlas.Order20160A8.Bivectors
open scoped Kronecker MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
/-- Coordinates of the natural module tensored with its exterior square. -/
abbrev Space := (Fin 4 × Fin 6) → ZMod 2

/-- The actual natural matrix tensored with its second compound matrix. -/
def tensorMatrix (g : Group) : Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) (ZMod 2) :=
  g.val ⊗ₖ compound g.val

private theorem compound_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    compound (A * B) = compound A * compound B := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  exact exteriorMap_mul A B

private theorem compound_one : compound (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_one]
  exact exteriorMap_one

/-- The marked natural–exterior tensor representation of binary SL₄. -/
noncomputable def mixedTensor : Representation (ZMod 2) Group Space where
  toFun g := (tensorMatrix g).toLin'
  map_one' := by
    change (tensorMatrix 1).toLin' = LinearMap.id
    simp only [tensorMatrix, Matrix.SpecialLinearGroup.coe_one, compound_one,
      Matrix.one_kronecker_one, Matrix.toLin'_one]
  map_mul' g h := by
    change (tensorMatrix (g * h)).toLin' =
      (tensorMatrix g).toLin'.comp (tensorMatrix h).toLin'
    rw [tensorMatrix, Matrix.SpecialLinearGroup.coe_mul, compound_mul,
      Matrix.mul_kronecker_mul, Matrix.toLin'_mul]
    rfl

private theorem swap0_matrix : (simpleSwap 0).val =
    !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] := by decide
private theorem swap1_matrix : (simpleSwap 1).val =
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] := by decide

/-- Reversed proper adjacent support has zero highest space in the full mixed tensor. -/
theorem mixedTensor_reverse_highest_eq_zero
    (x : Space) (h : LocalHighestVector mixedTensor {1, 2} x) : x = 0 := by
  have u0 := h.upper_fixed 0 1 (by decide)
  have u1 := h.upper_fixed 1 2 (by decide)
  have u2 := h.upper_fixed 2 3 (by decide)
  have s0 := h.inactive_fixed 0 (by decide)
  have a1 := h.active_relation 1 (by decide)
  have h0 := congrFun u0 (0,0)
  have h1 := congrFun u0 (0,1)
  have h2 := congrFun u0 (0,2)
  have h3 := congrFun u0 (0,3)
  have h4 := congrFun u0 (0,4)
  have h5 := congrFun u0 (0,5)
  have h6 := congrFun u0 (2,1)
  have h7 := congrFun u0 (2,2)
  have h8 := congrFun u0 (3,1)
  have h9 := congrFun u0 (3,2)
  have h10 := congrFun u1 (0,0)
  have h11 := congrFun u1 (0,4)
  have h12 := congrFun u1 (1,0)
  have h13 := congrFun u1 (1,1)
  have h14 := congrFun u1 (1,2)
  have h15 := congrFun u1 (1,4)
  have h16 := congrFun u1 (3,0)
  have h17 := congrFun u1 (3,4)
  have h18 := congrFun u2 (0,1)
  have h19 := congrFun u2 (0,3)
  have h20 := congrFun u2 (2,0)
  have h21 := congrFun u2 (2,1)
  have h22 := congrFun s0 (0,0)
  have h23 := congrFun a1 (0,3)
  simp [mixedTensor, tensorMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.kroneckerMap,
    compound, first, second, simpleLower, swap0_matrix, swap1_matrix,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  simp only [CharTwo.add_self_eq_zero, zero_add] at h23
  have hx00 : x (0,0) = 0 := h22.symm.trans h0
  have hx11 : x (1,1) = 0 := by simpa [h10, h23, h3] using h1
  have hx12 : x (1,2) = 0 := by simpa [h18, h19, h4] using h2
  have hx20 : x (2,0) = 0 := by simpa [h0, hx11, h13] using h12
  have hx25 : x (2,5) = 0 := by simpa [h4, h5, h7] using h15
  have hx32 : x (3,2) = 0 := by simpa [h13, h14, h16] using h21
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · exact hx00
  · exact h10
  · exact h18
  · exact h23
  · exact h19
  · exact h11
  · exact h0
  · exact hx11
  · exact hx12
  · exact h3
  · exact h4
  · exact h5
  · exact hx20
  · exact h13
  · exact h14
  · exact h6
  · exact h7
  · exact hx25
  · exact h20
  · exact h16
  · exact hx32
  · exact h8
  · exact h9
  · exact h17

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation
