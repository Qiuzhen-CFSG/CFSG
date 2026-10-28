module
public import Theory.Representation.BinaryFifteenPoint.SingerQuotientCoordinates
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Both reciprocal cubic kernel ranks on all fifteen-point quotient rows

All eight quotient rows are retained. Each rank is certified by explicit
invertible row and column changes reducing the cubic matrix to a diagonal
matrix. The arithmetic is checked by the Lean kernel, not a native oracle.
-/
@[expose] public noncomputable section
namespace BinaryFifteenPoint
open Matrix Polynomial Thompson.BinaryMatrix

/-- False means X³+X+1; true means the reciprocal X³+X²+1. -/
def singerCubic (reciprocal : Bool) : (ZMod 2)[X] :=
  if reciprocal then X^3+X^2+1 else X^3+X+1

/-- The two kernel-dimension tables in the frozen eight-row order. -/
def singerCubicKernelDimension (reciprocal : Bool) : Fin 8 → ℕ :=
  if reciprocal then ![6,6,3,3,0,0,0,0] else ![6,6,6,6,3,3,0,0]

private def cubicRank (reciprocal : Bool) (r : Fin 8) : ℕ :=
  quotientDimension r-singerCubicKernelDimension reciprocal r

private def squareRows : Array (Array ℕ) := #[#[1, 8272, 26654, 88, 72, 8, 104, 5920, 20166, 16528, 1298, 20482, 10330, 10284, 22604], #[4136, 13327, 44, 36, 4, 52, 2960, 10083, 8264, 649, 10241, 5165, 5142, 11302], #[1, 512, 1670, 368, 1262, 1032, 82, 1282, 642, 644, 1412], #[256, 835, 184, 631, 516, 41, 641, 321, 322, 706], #[1, 28, 26, 2, 20], #[14, 13, 1, 10], #[1], #[]]
private def cubeRows : Array (Array ℕ) := #[#[1, 22558, 28704, 80, 56, 40, 72, 17632, 32058, 15750, 10986, 6216, 8288, 26682, 22], #[11279, 14352, 40, 28, 20, 36, 8816, 16029, 7875, 5493, 3108, 4144, 13341, 11], #[1, 1414, 1792, 1096, 2002, 990, 682, 384, 512, 1666, 6], #[707, 896, 548, 1001, 495, 341, 192, 256, 833, 3], #[1, 18, 20, 22, 10], #[9, 10, 11, 5], #[1], #[]]
private def cubicRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 30796, 6202, 0, 96, 0, 96, 21312, 13052, 32534, 11256, 16458, 6202, 24598, 6234], #[15398, 3101, 0, 48, 0, 48, 10656, 6526, 16267, 5628, 8229, 3101, 12299, 3117], #[1, 1924, 386, 1328, 812, 2038, 696, 1026, 386, 1542, 386], #[962, 193, 664, 406, 1019, 348, 513, 193, 771, 193], #[1, 12, 10, 28, 14], #[6, 5, 14, 7], #[1], #[]] else #[#[1, 28798, 4116, 112, 64, 120, 24, 18926, 24642, 31164, 12402, 16508, 12330, 4188, 28790], #[14399, 2058, 56, 32, 60, 12, 9463, 12321, 15582, 6201, 8254, 6165, 2094, 14395], #[1, 1798, 260, 1182, 1538, 1948, 770, 1028, 770, 260, 1798], #[899, 130, 591, 769, 974, 385, 514, 385, 130, 899], #[1, 6, 0, 6, 0], #[3, 0, 3, 0], #[1], #[]]
private def leftRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 2, 4, 16, 128, 402, 534, 1410, 2960, 80, 8, 32, 4100, 8214, 16404], #[1, 2, 8, 64, 201, 267, 705, 1480, 40, 4, 16, 2050, 4107, 8202], #[1, 2, 4, 8, 18, 46, 90, 132, 260, 518, 1028], #[1, 2, 4, 9, 23, 45, 66, 130, 259, 514], #[1, 2, 4, 10, 22], #[1, 2, 5, 11], #[1], #[]] else #[#[1, 2, 4, 8, 16, 40, 112, 234, 694, 350, 1776, 2810, 4768, 8252, 16426], #[1, 2, 4, 8, 20, 56, 117, 347, 175, 888, 1405, 2384, 4126, 8213], #[1, 2, 4, 10, 46, 22, 104, 170, 296, 516, 1026], #[1, 2, 5, 23, 11, 52, 85, 148, 258, 513], #[1, 2, 4, 10, 16], #[1, 2, 5, 8], #[1], #[]]
private def rightRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 16316, 1746, 12928, 22880, 19544, 19536, 24320, 7744, 512, 1024, 2048, 4096, 8192, 16384], #[8158, 873, 6464, 11440, 9772, 9768, 12160, 3872, 256, 512, 1024, 2048, 4096, 8192], #[1, 1156, 642, 720, 1608, 832, 416, 1408, 256, 512, 1024], #[578, 321, 360, 804, 416, 208, 704, 128, 256, 512], #[1, 20, 18, 16, 8], #[10, 9, 8, 4], #[1], #[]] else #[#[1, 24694, 16732, 32, 88, 64, 16, 31104, 4096, 512, 1024, 2048, 16640, 8192, 16384], #[12347, 8366, 16, 44, 32, 8, 15552, 2048, 256, 512, 1024, 8320, 4096, 8192], #[1, 1542, 1044, 1944, 256, 32, 64, 128, 1040, 512, 1024], #[771, 522, 972, 128, 16, 32, 64, 520, 256, 512], #[1, 6, 4, 8, 16], #[3, 2, 4, 8], #[1], #[]]
private def leftInverseRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 2, 4, 1024, 8, 2048, 520, 16, 58, 78, 168, 364, 4100, 8206, 16396], #[1, 2, 512, 4, 1024, 260, 8, 29, 39, 84, 182, 2050, 4103, 8198], #[1, 2, 4, 8, 18, 46, 88, 132, 260, 518, 1028], #[1, 2, 4, 9, 23, 44, 66, 130, 259, 514], #[1, 2, 4, 10, 22], #[1, 2, 5, 11], #[1], #[]] else #[#[1, 2, 4, 8, 16, 40, 120, 218, 614, 484, 1406, 2420, 4374, 8244, 16418], #[1, 2, 4, 8, 20, 60, 109, 307, 242, 703, 1210, 2187, 4122, 8209], #[1, 2, 4, 10, 38, 28, 86, 148, 278, 516, 1026], #[1, 2, 5, 19, 14, 43, 74, 139, 258, 513], #[1, 2, 4, 10, 16], #[1, 2, 5, 8], #[1], #[]]
private def rightInverseRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 30796, 6202, 96, 21312, 6544, 7936, 12808, 24192, 512, 1024, 2048, 4096, 8192, 16384], #[15398, 3101, 48, 10656, 3272, 3968, 6404, 12096, 256, 512, 1024, 2048, 4096, 8192], #[1, 1924, 386, 1328, 1192, 1216, 800, 1408, 256, 512, 1024], #[962, 193, 664, 596, 608, 400, 704, 128, 256, 512], #[1, 12, 10, 16, 8], #[6, 5, 8, 4], #[1], #[]] else #[#[1, 28798, 4116, 112, 64, 8, 32, 14720, 20480, 512, 1024, 2048, 256, 8192, 16384], #[14399, 2058, 56, 32, 4, 16, 7360, 10240, 256, 512, 1024, 128, 4096, 8192], #[1, 1798, 260, 920, 1280, 32, 64, 128, 16, 512, 1024], #[899, 130, 460, 640, 16, 32, 64, 8, 256, 512], #[1, 6, 4, 8, 16], #[3, 2, 4, 8], #[1], #[]]
private def leftProductRows (reciprocal : Bool) : Array (Array ℕ) :=
  if reciprocal then #[#[1, 30796, 6202, 96, 21312, 6544, 7936, 12808, 24192, 0, 0, 0, 0, 0, 0], #[15398, 3101, 48, 10656, 3272, 3968, 6404, 12096, 0, 0, 0, 0, 0, 0], #[1, 1924, 386, 1328, 1192, 1216, 800, 1408, 0, 0, 0], #[962, 193, 664, 596, 608, 400, 704, 0, 0, 0], #[1, 12, 10, 16, 8], #[6, 5, 8, 4], #[1], #[]] else #[#[1, 28798, 4116, 112, 64, 8, 32, 14720, 20480, 0, 0, 0, 0, 0, 0], #[14399, 2058, 56, 32, 4, 16, 7360, 10240, 0, 0, 0, 0, 0, 0], #[1, 1798, 260, 920, 1280, 0, 0, 0, 0, 0, 0], #[899, 130, 460, 640, 0, 0, 0, 0, 0, 0], #[1, 6, 0, 0, 0], #[3, 0, 0, 0], #[1], #[]]

private theorem square_check : ∀ (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct (singerQuotientRows[r.val]!)[i.val]! singerQuotientRows[r.val]!
      (quotientDimension r)=(squareRows[r.val]!)[i.val]! := by decide +kernel
private theorem cube_check : ∀ (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct (squareRows[r.val]!)[i.val]! singerQuotientRows[r.val]!
      (quotientDimension r)=(cubeRows[r.val]!)[i.val]! := by decide +kernel
private theorem cubic_entry_check : ∀ (b : Bool) (r : Fin 8) (i j : Fin (quotientDimension r)),
    ((cubicRows b)[r.val]!)[i.val]!.testBit j.val =
      (((cubeRows[r.val]!)[i.val]!.testBit j.val !=
        (if b then (squareRows[r.val]!)[i.val]!.testBit j.val
         else (singerQuotientRows[r.val]!)[i.val]!.testBit j.val)) != decide (i=j)) := by
  decide +kernel

private theorem cubic_matrix (b : Bool) (r : Fin 8) :
    aeval (singerQuotientMatrix r) (singerCubic b)=
      decode (quotientDimension r) (cubicRows b)[r.val]! := by
  have hsq : (singerQuotientMatrix r)^2=decode (quotientDimension r) squareRows[r.val]! := by
    rw [pow_two]
    exact decode_mul _ _ _ _ (square_check r)
  have hcu : (singerQuotientMatrix r)^3=decode (quotientDimension r) cubeRows[r.val]! := by
    rw [show (3 : ℕ)=2+1 from rfl,pow_succ,hsq]
    exact decode_mul _ _ _ _ (cube_check r)
  cases b <;> simp only [singerCubic,Bool.false_eq_true,ite_false,ite_true,
    map_add,map_pow,map_one,aeval_X,hcu,hsq]
  all_goals
    ext i j
    change bit (cubeRows[r.val]!)[i.val]! j.val + _ +
      (if i=j then (1 : ZMod 2) else 0) = bit _ j.val
    simp only [singerQuotientMatrix,decode,bit,cubic_entry_check]
    split <;> split <;> by_cases hij : i=j <;> simp_all <;> decide

private theorem left_inverse_check : ∀ (b : Bool) (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct ((leftInverseRows b)[r.val]!)[i.val]! (leftRows b)[r.val]!
      (quotientDimension r)=2^i.val := by decide +kernel
private theorem right_inverse_check : ∀ (b : Bool) (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct ((rightRows b)[r.val]!)[i.val]! (rightInverseRows b)[r.val]!
      (quotientDimension r)=2^i.val := by decide +kernel
private theorem left_product_check : ∀ (b : Bool) (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct ((leftRows b)[r.val]!)[i.val]! (cubicRows b)[r.val]!
      (quotientDimension r)=((leftProductRows b)[r.val]!)[i.val]! := by decide +kernel
private theorem normal_form_check : ∀ (b : Bool) (r : Fin 8) (i : Fin (quotientDimension r)),
    rowProduct ((leftProductRows b)[r.val]!)[i.val]! (rightRows b)[r.val]!
      (quotientDimension r)=if i.val<cubicRank b r then 2^i.val else 0 := by decide +kernel

private theorem normal_form (b : Bool) (r : Fin 8) :
    decode (quotientDimension r) (leftRows b)[r.val]! *
      decode (quotientDimension r) (cubicRows b)[r.val]! *
      decode (quotientDimension r) (rightRows b)[r.val]! =
        diagonal (fun i : Fin (quotientDimension r) => if i.val<cubicRank b r then 1 else 0) := by
  rw [decode_mul _ _ _ _ (left_product_check b r)]
  ext i j
  change (∑ k : Fin (quotientDimension r), bit ((leftProductRows b)[r.val]!)[i.val]! k.val *
    bit ((rightRows b)[r.val]!)[k.val]! j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun k => bit ((leftProductRows b)[r.val]!)[i.val]! k *
    bit ((rightRows b)[r.val]!)[k]! j.val),←bit_rowProduct,normal_form_check]
  by_cases hi : i.val<cubicRank b r
  · simp [hi,bit,Nat.testBit_two_pow,Matrix.diagonal_apply,Fin.ext_iff,eq_comm]
  · simp [hi,bit,Matrix.diagonal_apply]

private theorem rank_of_normal_form {n : ℕ}
    (A L R LI RI D : Matrix (Fin n) (Fin n) (ZMod 2))
    (hL : LI*L=1) (hR : R*RI=1) (hD : L*A*R=D) : A.rank=D.rank := by
  have he : A=LI*D*RI := by
    rw [←hD]
    simp only [←Matrix.mul_assoc,hL,Matrix.one_mul]
    rw [Matrix.mul_assoc,hR,Matrix.mul_one]
  apply le_antisymm
  · rw [he]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [←hD]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

private theorem cubic_rank (b : Bool) (r : Fin 8) :
    (aeval (singerQuotientMatrix r) (singerCubic b)).rank=cubicRank b r := by
  rw [cubic_matrix]
  rw [rank_of_normal_form _ _ _ _ _ _
    (decode_mul_one _ _ _ (left_inverse_check b r))
    (decode_mul_one _ _ _ (right_inverse_check b r)) (normal_form b r),rank_diagonal]
  exact (by decide +kernel : ∀ (b : Bool) (r : Fin 8),
    Fintype.card {i : Fin (quotientDimension r) //
      (if i.val<cubicRank b r then (1 : ZMod 2) else 0)≠0}=cubicRank b r) b r

private theorem row_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (k : ℕ) (x : Fin n → ZMod 2) : (A.vecMulLinear^k) x=x ᵥ* A^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    change (x ᵥ* A^k) ᵥ* A=x ᵥ* A^(k+1)
    rw [vecMul_vecMul,pow_succ]

private theorem row_aeval {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (p : (ZMod 2)[X]) : aeval A.vecMulLinear p=(aeval A p).vecMulLinear := by
  apply LinearMap.ext
  intro x
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,LinearMap.add_apply,Matrix.vecMulLinear_apply,hp,hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial,Module.End.mul_apply,Module.algebraMap_end_apply,
      Matrix.vecMulLinear_apply,row_pow,←vecMul_vecMul]
    simp [Algebra.algebraMap_eq_smul_one,vecMul_smul,smul_vecMul]

/-- Exact kernel dimensions for both reciprocal cubics, on every quotient
row including the one-dimensional and zero quotients. -/
theorem singerQuotient_cubic_kernel_finrank (b : Bool) (r : Fin 8) :
    Module.finrank (ZMod 2) (LinearMap.ker
      (aeval (singerQuotientMatrix r).vecMulLinear (singerCubic b)))=
        singerCubicKernelDimension b r := by
  rw [row_aeval]
  have h := (aeval (singerQuotientMatrix r) (singerCubic b)).vecMulLinear.finrank_range_add_finrank_ker
  have hr : Module.finrank (ZMod 2) (LinearMap.range
      (aeval (singerQuotientMatrix r) (singerCubic b)).vecMulLinear)=cubicRank b r := by
    rw [←Matrix.mulVecLin_transpose,←Matrix.rank,Matrix.rank_transpose,cubic_rank]
  rw [hr,Module.finrank_fin_fun] at h
  have hn : cubicRank b r+singerCubicKernelDimension b r=quotientDimension r :=
    (by decide +kernel : ∀ (b : Bool) (r : Fin 8),
      cubicRank b r+singerCubicKernelDimension b r=quotientDimension r) b r
  exact Nat.add_left_cancel (h.trans hn.symm)

end BinaryFifteenPoint
