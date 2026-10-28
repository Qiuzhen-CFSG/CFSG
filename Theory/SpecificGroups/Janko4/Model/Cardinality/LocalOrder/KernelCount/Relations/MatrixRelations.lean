module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.MaskProducts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.ActionProducts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.CommuteProducts
import Mathlib.Tactic.FinCases

/-!
# Matrix identities for the local kernel

These witnesses implement the ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup` and the conjugates in `KernelCount.BinarySpan`.
Packed products are checked by Lean's kernel; `decode_packedMul` transfers
these certificates to binary matrices. No external computation is trusted.
-/

public section
namespace Janko4.Cardinality.KernelCount.Relations
open Janko4.GeneratorCertificates

lemma decoded_common {a b c d z : Vector ℕ 112}
    (h : packedMul a b = z) (k : packedMul c d = z) :
    decodeRows a * decodeRows b = decodeRows c * decodeRows d := by
  rw [decoded_product h, decoded_product k]

lemma matrix_x0 : decodeRows e0Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e1Rows :=
  decoded_common product_x0left product_x0right

lemma matrix_x1 : decodeRows e1Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e0Rows :=
  decoded_common product_x1left product_x1right

lemma matrix_x2 : decodeRows e2Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e3Rows :=
  decoded_common product_x2left product_x2right

lemma matrix_x3 : decodeRows e3Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e2Rows :=
  decoded_common product_x3left product_x3right

lemma matrix_x4 : decodeRows e4Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e4Rows :=
  decoded_common product_x4left product_x4right

lemma matrix_x5 : decodeRows e5Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e6Rows :=
  decoded_common product_x5left product_x5right

lemma matrix_x6 : decodeRows e6Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e5Rows :=
  decoded_common product_x6left product_x6right

lemma matrix_x7 : decodeRows e7Rows * decodeRows xRows =
    decodeRows xRows * decodeRows m224_5Rows :=
  decoded_common product_x7left product_x7right

lemma matrix_x8 : decodeRows e8Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e9Rows :=
  decoded_common product_x8left product_x8right

lemma matrix_x9 : decodeRows e9Rows * decodeRows xRows =
    decodeRows xRows * decodeRows e8Rows :=
  decoded_common product_x9left product_x9right

lemma matrix_x10 : decodeRows e10Rows * decodeRows xRows =
    decodeRows xRows * decodeRows m1952_5Rows :=
  decoded_common product_x10left product_x10right

lemma expand_x0 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 0).testBit j.val) = e 1 := by
  have h : (fun j : Fin 11 => (xMasks 0).testBit j.val) = ![false, true, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x0 : matrixProduct (fun j => (xMasks 0).testBit j.val) =
    decodeRows e1Rows := by
  exact expand_x0 (fun j => decodeRows (basisRows j))

lemma expand_x1 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 1).testBit j.val) = e 0 := by
  have h : (fun j : Fin 11 => (xMasks 1).testBit j.val) = ![true, false, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x1 : matrixProduct (fun j => (xMasks 1).testBit j.val) =
    decodeRows e0Rows := by
  exact expand_x1 (fun j => decodeRows (basisRows j))

lemma expand_x2 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 2).testBit j.val) = e 3 := by
  have h : (fun j : Fin 11 => (xMasks 2).testBit j.val) = ![false, false, false, true, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x2 : matrixProduct (fun j => (xMasks 2).testBit j.val) =
    decodeRows e3Rows := by
  exact expand_x2 (fun j => decodeRows (basisRows j))

lemma expand_x3 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 3).testBit j.val) = e 2 := by
  have h : (fun j : Fin 11 => (xMasks 3).testBit j.val) = ![false, false, true, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x3 : matrixProduct (fun j => (xMasks 3).testBit j.val) =
    decodeRows e2Rows := by
  exact expand_x3 (fun j => decodeRows (basisRows j))

lemma expand_x4 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 4).testBit j.val) = e 4 := by
  have h : (fun j : Fin 11 => (xMasks 4).testBit j.val) = ![false, false, false, false, true, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x4 : matrixProduct (fun j => (xMasks 4).testBit j.val) =
    decodeRows e4Rows := by
  exact expand_x4 (fun j => decodeRows (basisRows j))

lemma expand_x5 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 5).testBit j.val) = e 6 := by
  have h : (fun j : Fin 11 => (xMasks 5).testBit j.val) = ![false, false, false, false, false, false, true, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x5 : matrixProduct (fun j => (xMasks 5).testBit j.val) =
    decodeRows e6Rows := by
  exact expand_x5 (fun j => decodeRows (basisRows j))

lemma expand_x6 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 6).testBit j.val) = e 5 := by
  have h : (fun j : Fin 11 => (xMasks 6).testBit j.val) = ![false, false, false, false, false, true, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x6 : matrixProduct (fun j => (xMasks 6).testBit j.val) =
    decodeRows e5Rows := by
  exact expand_x6 (fun j => decodeRows (basisRows j))

lemma expand_x7 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 7).testBit j.val) = e 5 * (e 6 * (e 7)) := by
  have h : (fun j : Fin 11 => (xMasks 7).testBit j.val) = ![false, false, false, false, false, true, true, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x7 : matrixProduct (fun j => (xMasks 7).testBit j.val) =
    decodeRows m224_5Rows := by
  rw [← decoded_product product_m224_5, ← decoded_product product_m224_6]
  exact expand_x7 (fun j => decodeRows (basisRows j))

lemma expand_x8 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 8).testBit j.val) = e 9 := by
  have h : (fun j : Fin 11 => (xMasks 8).testBit j.val) = ![false, false, false, false, false, false, false, false, false, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x8 : matrixProduct (fun j => (xMasks 8).testBit j.val) =
    decodeRows e9Rows := by
  exact expand_x8 (fun j => decodeRows (basisRows j))

lemma expand_x9 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 9).testBit j.val) = e 8 := by
  have h : (fun j : Fin 11 => (xMasks 9).testBit j.val) = ![false, false, false, false, false, false, false, false, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x9 : matrixProduct (fun j => (xMasks 9).testBit j.val) =
    decodeRows e8Rows := by
  exact expand_x9 (fun j => decodeRows (basisRows j))

lemma expand_x10 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (xMasks 10).testBit j.val) = e 5 * (e 7 * (e 8 * (e 9 * (e 10)))) := by
  have h : (fun j : Fin 11 => (xMasks 10).testBit j.val) = ![false, false, false, false, false, true, false, true, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_x10 : matrixProduct (fun j => (xMasks 10).testBit j.val) =
    decodeRows m1952_5Rows := by
  rw [← decoded_product product_m1952_5, ← decoded_product product_m1952_7, ← decoded_product product_m1952_8, ← decoded_product product_m1952_9]
  exact expand_x10 (fun j => decodeRows (basisRows j))

lemma matrix_action_x (i : Fin 11) :
    decodeRows (basisRows i) * decodeRows xRows =
      decodeRows xRows * matrixProduct (fun j => (xMasks i).testBit j.val) := by
  fin_cases i
  · exact matrix_x0.trans (congrArg (decodeRows xRows * ·) mask_x0.symm)
  · exact matrix_x1.trans (congrArg (decodeRows xRows * ·) mask_x1.symm)
  · exact matrix_x2.trans (congrArg (decodeRows xRows * ·) mask_x2.symm)
  · exact matrix_x3.trans (congrArg (decodeRows xRows * ·) mask_x3.symm)
  · exact matrix_x4.trans (congrArg (decodeRows xRows * ·) mask_x4.symm)
  · exact matrix_x5.trans (congrArg (decodeRows xRows * ·) mask_x5.symm)
  · exact matrix_x6.trans (congrArg (decodeRows xRows * ·) mask_x6.symm)
  · exact matrix_x7.trans (congrArg (decodeRows xRows * ·) mask_x7.symm)
  · exact matrix_x8.trans (congrArg (decodeRows xRows * ·) mask_x8.symm)
  · exact matrix_x9.trans (congrArg (decodeRows xRows * ·) mask_x9.symm)
  · exact matrix_x10.trans (congrArg (decodeRows xRows * ·) mask_x10.symm)

lemma matrix_y0 : decodeRows e0Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e2Rows :=
  decoded_common product_y0left product_y0right

lemma matrix_y1 : decodeRows e1Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e0Rows :=
  decoded_common product_y1left product_y1right

lemma matrix_y2 : decodeRows e2Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e1Rows :=
  decoded_common product_y2left product_y2right

lemma matrix_y3 : decodeRows e3Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e4Rows :=
  decoded_common product_y3left product_y3right

lemma matrix_y4 : decodeRows e4Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e5Rows :=
  decoded_common product_y4left product_y4right

lemma matrix_y5 : decodeRows e5Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e3Rows :=
  decoded_common product_y5left product_y5right

lemma matrix_y6 : decodeRows e6Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e7Rows :=
  decoded_common product_y6left product_y6right

lemma matrix_y7 : decodeRows e7Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e8Rows :=
  decoded_common product_y7left product_y7right

lemma matrix_y8 : decodeRows e8Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e6Rows :=
  decoded_common product_y8left product_y8right

lemma matrix_y9 : decodeRows e9Rows * decodeRows yRows =
    decodeRows yRows * decodeRows e10Rows :=
  decoded_common product_y9left product_y9right

lemma matrix_y10 : decodeRows e10Rows * decodeRows yRows =
    decodeRows yRows * decodeRows m1991_0Rows :=
  decoded_common product_y10left product_y10right

lemma expand_y0 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 0).testBit j.val) = e 2 := by
  have h : (fun j : Fin 11 => (yMasks 0).testBit j.val) = ![false, false, true, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y0 : matrixProduct (fun j => (yMasks 0).testBit j.val) =
    decodeRows e2Rows := by
  exact expand_y0 (fun j => decodeRows (basisRows j))

lemma expand_y1 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 1).testBit j.val) = e 0 := by
  have h : (fun j : Fin 11 => (yMasks 1).testBit j.val) = ![true, false, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y1 : matrixProduct (fun j => (yMasks 1).testBit j.val) =
    decodeRows e0Rows := by
  exact expand_y1 (fun j => decodeRows (basisRows j))

lemma expand_y2 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 2).testBit j.val) = e 1 := by
  have h : (fun j : Fin 11 => (yMasks 2).testBit j.val) = ![false, true, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y2 : matrixProduct (fun j => (yMasks 2).testBit j.val) =
    decodeRows e1Rows := by
  exact expand_y2 (fun j => decodeRows (basisRows j))

lemma expand_y3 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 3).testBit j.val) = e 4 := by
  have h : (fun j : Fin 11 => (yMasks 3).testBit j.val) = ![false, false, false, false, true, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y3 : matrixProduct (fun j => (yMasks 3).testBit j.val) =
    decodeRows e4Rows := by
  exact expand_y3 (fun j => decodeRows (basisRows j))

lemma expand_y4 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 4).testBit j.val) = e 5 := by
  have h : (fun j : Fin 11 => (yMasks 4).testBit j.val) = ![false, false, false, false, false, true, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y4 : matrixProduct (fun j => (yMasks 4).testBit j.val) =
    decodeRows e5Rows := by
  exact expand_y4 (fun j => decodeRows (basisRows j))

lemma expand_y5 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 5).testBit j.val) = e 3 := by
  have h : (fun j : Fin 11 => (yMasks 5).testBit j.val) = ![false, false, false, true, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y5 : matrixProduct (fun j => (yMasks 5).testBit j.val) =
    decodeRows e3Rows := by
  exact expand_y5 (fun j => decodeRows (basisRows j))

lemma expand_y6 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 6).testBit j.val) = e 7 := by
  have h : (fun j : Fin 11 => (yMasks 6).testBit j.val) = ![false, false, false, false, false, false, false, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y6 : matrixProduct (fun j => (yMasks 6).testBit j.val) =
    decodeRows e7Rows := by
  exact expand_y6 (fun j => decodeRows (basisRows j))

lemma expand_y7 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 7).testBit j.val) = e 8 := by
  have h : (fun j : Fin 11 => (yMasks 7).testBit j.val) = ![false, false, false, false, false, false, false, false, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y7 : matrixProduct (fun j => (yMasks 7).testBit j.val) =
    decodeRows e8Rows := by
  exact expand_y7 (fun j => decodeRows (basisRows j))

lemma expand_y8 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 8).testBit j.val) = e 6 := by
  have h : (fun j : Fin 11 => (yMasks 8).testBit j.val) = ![false, false, false, false, false, false, true, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y8 : matrixProduct (fun j => (yMasks 8).testBit j.val) =
    decodeRows e6Rows := by
  exact expand_y8 (fun j => decodeRows (basisRows j))

lemma expand_y9 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 9).testBit j.val) = e 10 := by
  have h : (fun j : Fin 11 => (yMasks 9).testBit j.val) = ![false, false, false, false, false, false, false, false, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y9 : matrixProduct (fun j => (yMasks 9).testBit j.val) =
    decodeRows e10Rows := by
  exact expand_y9 (fun j => decodeRows (basisRows j))

lemma expand_y10 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (yMasks 10).testBit j.val) = e 0 * (e 1 * (e 2 * (e 6 * (e 7 * (e 8 * (e 9 * (e 10))))))) := by
  have h : (fun j : Fin 11 => (yMasks 10).testBit j.val) = ![true, true, true, false, false, false, true, true, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma mask_y10 : matrixProduct (fun j => (yMasks 10).testBit j.val) =
    decodeRows m1991_0Rows := by
  rw [← decoded_product product_m1991_0, ← decoded_product product_m1991_1, ← decoded_product product_m1991_2, ← decoded_product product_m1991_6, ← decoded_product product_m1991_7, ← decoded_product product_m1991_8, ← decoded_product product_m1991_9]
  exact expand_y10 (fun j => decodeRows (basisRows j))

lemma matrix_action_y (i : Fin 11) :
    decodeRows (basisRows i) * decodeRows yRows =
      decodeRows yRows * matrixProduct (fun j => (yMasks i).testBit j.val) := by
  fin_cases i
  · exact matrix_y0.trans (congrArg (decodeRows yRows * ·) mask_y0.symm)
  · exact matrix_y1.trans (congrArg (decodeRows yRows * ·) mask_y1.symm)
  · exact matrix_y2.trans (congrArg (decodeRows yRows * ·) mask_y2.symm)
  · exact matrix_y3.trans (congrArg (decodeRows yRows * ·) mask_y3.symm)
  · exact matrix_y4.trans (congrArg (decodeRows yRows * ·) mask_y4.symm)
  · exact matrix_y5.trans (congrArg (decodeRows yRows * ·) mask_y5.symm)
  · exact matrix_y6.trans (congrArg (decodeRows yRows * ·) mask_y6.symm)
  · exact matrix_y7.trans (congrArg (decodeRows yRows * ·) mask_y7.symm)
  · exact matrix_y8.trans (congrArg (decodeRows yRows * ·) mask_y8.symm)
  · exact matrix_y9.trans (congrArg (decodeRows yRows * ·) mask_y9.symm)
  · exact matrix_y10.trans (congrArg (decodeRows yRows * ·) mask_y10.symm)

lemma matrix_commute (i j : Fin 11) :
    Commute (decodeRows (basisRows i)) (decodeRows (basisRows j)) := by
  fin_cases i
  · fin_cases j
    · exact Commute.refl _
    · exact decoded_common product_comm0_1 product_comm1_0
    · exact decoded_common product_comm0_2 product_comm2_0
    · exact decoded_common product_comm0_3 product_comm3_0
    · exact decoded_common product_comm0_4 product_comm4_0
    · exact decoded_common product_comm0_5 product_comm5_0
    · exact decoded_common product_comm0_6 product_comm6_0
    · exact decoded_common product_comm0_7 product_comm7_0
    · exact decoded_common product_comm0_8 product_comm8_0
    · exact decoded_common product_comm0_9 product_comm9_0
    · exact decoded_common product_comm0_10 product_comm10_0
  · fin_cases j
    · exact decoded_common product_comm1_0 product_comm0_1
    · exact Commute.refl _
    · exact decoded_common product_comm1_2 product_comm2_1
    · exact decoded_common product_comm1_3 product_comm3_1
    · exact decoded_common product_comm1_4 product_comm4_1
    · exact decoded_common product_comm1_5 product_comm5_1
    · exact decoded_common product_comm1_6 product_comm6_1
    · exact decoded_common product_comm1_7 product_comm7_1
    · exact decoded_common product_comm1_8 product_comm8_1
    · exact decoded_common product_comm1_9 product_comm9_1
    · exact decoded_common product_comm1_10 product_comm10_1
  · fin_cases j
    · exact decoded_common product_comm2_0 product_comm0_2
    · exact decoded_common product_comm2_1 product_comm1_2
    · exact Commute.refl _
    · exact decoded_common product_comm2_3 product_comm3_2
    · exact decoded_common product_comm2_4 product_comm4_2
    · exact decoded_common product_comm2_5 product_comm5_2
    · exact decoded_common product_comm2_6 product_comm6_2
    · exact decoded_common product_comm2_7 product_comm7_2
    · exact decoded_common product_comm2_8 product_comm8_2
    · exact decoded_common product_comm2_9 product_comm9_2
    · exact decoded_common product_comm2_10 product_comm10_2
  · fin_cases j
    · exact decoded_common product_comm3_0 product_comm0_3
    · exact decoded_common product_comm3_1 product_comm1_3
    · exact decoded_common product_comm3_2 product_comm2_3
    · exact Commute.refl _
    · exact decoded_common product_comm3_4 product_comm4_3
    · exact decoded_common product_comm3_5 product_comm5_3
    · exact decoded_common product_comm3_6 product_comm6_3
    · exact decoded_common product_comm3_7 product_comm7_3
    · exact decoded_common product_comm3_8 product_comm8_3
    · exact decoded_common product_comm3_9 product_comm9_3
    · exact decoded_common product_comm3_10 product_comm10_3
  · fin_cases j
    · exact decoded_common product_comm4_0 product_comm0_4
    · exact decoded_common product_comm4_1 product_comm1_4
    · exact decoded_common product_comm4_2 product_comm2_4
    · exact decoded_common product_comm4_3 product_comm3_4
    · exact Commute.refl _
    · exact decoded_common product_comm4_5 product_comm5_4
    · exact decoded_common product_comm4_6 product_comm6_4
    · exact decoded_common product_comm4_7 product_comm7_4
    · exact decoded_common product_comm4_8 product_comm8_4
    · exact decoded_common product_comm4_9 product_comm9_4
    · exact decoded_common product_comm4_10 product_comm10_4
  · fin_cases j
    · exact decoded_common product_comm5_0 product_comm0_5
    · exact decoded_common product_comm5_1 product_comm1_5
    · exact decoded_common product_comm5_2 product_comm2_5
    · exact decoded_common product_comm5_3 product_comm3_5
    · exact decoded_common product_comm5_4 product_comm4_5
    · exact Commute.refl _
    · exact decoded_common product_comm5_6 product_comm6_5
    · exact decoded_common product_comm5_7 product_comm7_5
    · exact decoded_common product_comm5_8 product_comm8_5
    · exact decoded_common product_comm5_9 product_comm9_5
    · exact decoded_common product_comm5_10 product_comm10_5
  · fin_cases j
    · exact decoded_common product_comm6_0 product_comm0_6
    · exact decoded_common product_comm6_1 product_comm1_6
    · exact decoded_common product_comm6_2 product_comm2_6
    · exact decoded_common product_comm6_3 product_comm3_6
    · exact decoded_common product_comm6_4 product_comm4_6
    · exact decoded_common product_comm6_5 product_comm5_6
    · exact Commute.refl _
    · exact decoded_common product_comm6_7 product_comm7_6
    · exact decoded_common product_comm6_8 product_comm8_6
    · exact decoded_common product_comm6_9 product_comm9_6
    · exact decoded_common product_comm6_10 product_comm10_6
  · fin_cases j
    · exact decoded_common product_comm7_0 product_comm0_7
    · exact decoded_common product_comm7_1 product_comm1_7
    · exact decoded_common product_comm7_2 product_comm2_7
    · exact decoded_common product_comm7_3 product_comm3_7
    · exact decoded_common product_comm7_4 product_comm4_7
    · exact decoded_common product_comm7_5 product_comm5_7
    · exact decoded_common product_comm7_6 product_comm6_7
    · exact Commute.refl _
    · exact decoded_common product_comm7_8 product_comm8_7
    · exact decoded_common product_comm7_9 product_comm9_7
    · exact decoded_common product_comm7_10 product_comm10_7
  · fin_cases j
    · exact decoded_common product_comm8_0 product_comm0_8
    · exact decoded_common product_comm8_1 product_comm1_8
    · exact decoded_common product_comm8_2 product_comm2_8
    · exact decoded_common product_comm8_3 product_comm3_8
    · exact decoded_common product_comm8_4 product_comm4_8
    · exact decoded_common product_comm8_5 product_comm5_8
    · exact decoded_common product_comm8_6 product_comm6_8
    · exact decoded_common product_comm8_7 product_comm7_8
    · exact Commute.refl _
    · exact decoded_common product_comm8_9 product_comm9_8
    · exact decoded_common product_comm8_10 product_comm10_8
  · fin_cases j
    · exact decoded_common product_comm9_0 product_comm0_9
    · exact decoded_common product_comm9_1 product_comm1_9
    · exact decoded_common product_comm9_2 product_comm2_9
    · exact decoded_common product_comm9_3 product_comm3_9
    · exact decoded_common product_comm9_4 product_comm4_9
    · exact decoded_common product_comm9_5 product_comm5_9
    · exact decoded_common product_comm9_6 product_comm6_9
    · exact decoded_common product_comm9_7 product_comm7_9
    · exact decoded_common product_comm9_8 product_comm8_9
    · exact Commute.refl _
    · exact decoded_common product_comm9_10 product_comm10_9
  · fin_cases j
    · exact decoded_common product_comm10_0 product_comm0_10
    · exact decoded_common product_comm10_1 product_comm1_10
    · exact decoded_common product_comm10_2 product_comm2_10
    · exact decoded_common product_comm10_3 product_comm3_10
    · exact decoded_common product_comm10_4 product_comm4_10
    · exact decoded_common product_comm10_5 product_comm5_10
    · exact decoded_common product_comm10_6 product_comm6_10
    · exact decoded_common product_comm10_7 product_comm7_10
    · exact decoded_common product_comm10_8 product_comm8_10
    · exact decoded_common product_comm10_9 product_comm9_10
    · exact Commute.refl _

end Janko4.Cardinality.KernelCount.Relations
