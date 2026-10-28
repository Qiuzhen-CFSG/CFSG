module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Evaluations
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Masks

/-!
# Shared-subword certificates for the local presentation

The words and masks are from `UpperBound.Data` and its adjacent
`source/relator_masks.json`. The generator matrices implement the ATLAS
`J4G1-max1W1` program. Repeated subwords are factored into binary products;
all proposed products are checked by kernel reduction of packed arithmetic.
The external generator supplies witnesses only, never trusted evaluations.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
open KernelCount KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

lemma letters_0 : relatorLetters 0 = w184 := by decide +kernel
lemma evaluation_0 : representation hA hB (localRelator hA hB 0) =
    matrixProduct (fun j => (relatorMask 0).testBit j.val) := by
  change wordEval hA hB (relatorLetters 0) = _
  rw [letters_0, eval_w184]
  exact eval_mask0.symm

lemma letters_1 : relatorLetters 1 = w186 := by decide +kernel
lemma evaluation_1 : representation hA hB (localRelator hA hB 1) =
    matrixProduct (fun j => (relatorMask 1).testBit j.val) := by
  change wordEval hA hB (relatorLetters 1) = _
  rw [letters_1, eval_w186]
  exact eval_mask0.symm

lemma letters_2 : relatorLetters 2 = w191 := by decide +kernel
lemma evaluation_2 : representation hA hB (localRelator hA hB 2) =
    matrixProduct (fun j => (relatorMask 2).testBit j.val) := by
  change wordEval hA hB (relatorLetters 2) = _
  rw [letters_2, eval_w191]
  exact eval_mask2.symm

lemma letters_3 : relatorLetters 3 = w197 := by decide +kernel
lemma evaluation_3 : representation hA hB (localRelator hA hB 3) =
    matrixProduct (fun j => (relatorMask 3).testBit j.val) := by
  change wordEval hA hB (relatorLetters 3) = _
  rw [letters_3, eval_w197]
  exact eval_mask1348.symm

lemma letters_4 : relatorLetters 4 = w204 := by decide +kernel
lemma evaluation_4 : representation hA hB (localRelator hA hB 4) =
    matrixProduct (fun j => (relatorMask 4).testBit j.val) := by
  change wordEval hA hB (relatorLetters 4) = _
  rw [letters_4, eval_w204]
  exact eval_mask1018.symm

lemma letters_5 : relatorLetters 5 = w212 := by decide +kernel
lemma evaluation_5 : representation hA hB (localRelator hA hB 5) =
    matrixProduct (fun j => (relatorMask 5).testBit j.val) := by
  change wordEval hA hB (relatorLetters 5) = _
  rw [letters_5, eval_w212]
  exact eval_mask1366.symm

lemma letters_6 : relatorLetters 6 = w216 := by decide +kernel
lemma evaluation_6 : representation hA hB (localRelator hA hB 6) =
    matrixProduct (fun j => (relatorMask 6).testBit j.val) := by
  change wordEval hA hB (relatorLetters 6) = _
  rw [letters_6, eval_w216]
  exact eval_mask1485.symm

lemma letters_7 : relatorLetters 7 = w226 := by decide +kernel
lemma evaluation_7 : representation hA hB (localRelator hA hB 7) =
    matrixProduct (fun j => (relatorMask 7).testBit j.val) := by
  change wordEval hA hB (relatorLetters 7) = _
  rw [letters_7, eval_w226]
  exact eval_mask1166.symm

lemma letters_8 : relatorLetters 8 = w228 := by decide +kernel
lemma evaluation_8 : representation hA hB (localRelator hA hB 8) =
    matrixProduct (fun j => (relatorMask 8).testBit j.val) := by
  change wordEval hA hB (relatorLetters 8) = _
  rw [letters_8, eval_w228]
  exact eval_mask784.symm

lemma letters_9 : relatorLetters 9 = w236 := by decide +kernel
lemma evaluation_9 : representation hA hB (localRelator hA hB 9) =
    matrixProduct (fun j => (relatorMask 9).testBit j.val) := by
  change wordEval hA hB (relatorLetters 9) = _
  rw [letters_9, eval_w236]
  exact eval_mask901.symm

lemma letters_10 : relatorLetters 10 = w244 := by decide +kernel
lemma evaluation_10 : representation hA hB (localRelator hA hB 10) =
    matrixProduct (fun j => (relatorMask 10).testBit j.val) := by
  change wordEval hA hB (relatorLetters 10) = _
  rw [letters_10, eval_w244]
  exact eval_mask1301.symm

lemma letters_11 : relatorLetters 11 = w254 := by decide +kernel
lemma evaluation_11 : representation hA hB (localRelator hA hB 11) =
    matrixProduct (fun j => (relatorMask 11).testBit j.val) := by
  change wordEval hA hB (relatorLetters 11) = _
  rw [letters_11, eval_w254]
  exact eval_mask1388.symm

lemma letters_12 : relatorLetters 12 = w263 := by decide +kernel
lemma evaluation_12 : representation hA hB (localRelator hA hB 12) =
    matrixProduct (fun j => (relatorMask 12).testBit j.val) := by
  change wordEval hA hB (relatorLetters 12) = _
  rw [letters_12, eval_w263]
  exact eval_mask1154.symm

lemma letters_13 : relatorLetters 13 = w277 := by decide +kernel
lemma evaluation_13 : representation hA hB (localRelator hA hB 13) =
    matrixProduct (fun j => (relatorMask 13).testBit j.val) := by
  change wordEval hA hB (relatorLetters 13) = _
  rw [letters_13, eval_w277]
  exact eval_mask1105.symm

lemma letters_14 : relatorLetters 14 = w281 := by decide +kernel
lemma evaluation_14 : representation hA hB (localRelator hA hB 14) =
    matrixProduct (fun j => (relatorMask 14).testBit j.val) := by
  change wordEval hA hB (relatorLetters 14) = _
  rw [letters_14, eval_w281]
  exact eval_mask0.symm

lemma letters_15 : relatorLetters 15 = w290 := by decide +kernel
lemma evaluation_15 : representation hA hB (localRelator hA hB 15) =
    matrixProduct (fun j => (relatorMask 15).testBit j.val) := by
  change wordEval hA hB (relatorLetters 15) = _
  rw [letters_15, eval_w290]
  exact eval_mask411.symm

lemma letters_16 : relatorLetters 16 = w308 := by decide +kernel
lemma evaluation_16 : representation hA hB (localRelator hA hB 16) =
    matrixProduct (fun j => (relatorMask 16).testBit j.val) := by
  change wordEval hA hB (relatorLetters 16) = _
  rw [letters_16, eval_w308]
  exact eval_mask1969.symm

lemma letters_17 : relatorLetters 17 = w323 := by decide +kernel
lemma evaluation_17 : representation hA hB (localRelator hA hB 17) =
    matrixProduct (fun j => (relatorMask 17).testBit j.val) := by
  change wordEval hA hB (relatorLetters 17) = _
  rw [letters_17, eval_w323]
  exact eval_mask1184.symm

lemma letters_18 : relatorLetters 18 = w336 := by decide +kernel
lemma evaluation_18 : representation hA hB (localRelator hA hB 18) =
    matrixProduct (fun j => (relatorMask 18).testBit j.val) := by
  change wordEval hA hB (relatorLetters 18) = _
  rw [letters_18, eval_w336]
  exact eval_mask1991.symm

lemma letters_19 : relatorLetters 19 = w345 := by decide +kernel
lemma evaluation_19 : representation hA hB (localRelator hA hB 19) =
    matrixProduct (fun j => (relatorMask 19).testBit j.val) := by
  change wordEval hA hB (relatorLetters 19) = _
  rw [letters_19, eval_w345]
  exact eval_mask1465.symm

lemma letters_20 : relatorLetters 20 = w357 := by decide +kernel
lemma evaluation_20 : representation hA hB (localRelator hA hB 20) =
    matrixProduct (fun j => (relatorMask 20).testBit j.val) := by
  change wordEval hA hB (relatorLetters 20) = _
  rw [letters_20, eval_w357]
  exact eval_mask576.symm

lemma letters_21 : relatorLetters 21 = w367 := by decide +kernel
lemma evaluation_21 : representation hA hB (localRelator hA hB 21) =
    matrixProduct (fun j => (relatorMask 21).testBit j.val) := by
  change wordEval hA hB (relatorLetters 21) = _
  rw [letters_21, eval_w367]
  exact eval_mask1625.symm

lemma letters_22 : relatorLetters 22 = w384 := by decide +kernel
lemma evaluation_22 : representation hA hB (localRelator hA hB 22) =
    matrixProduct (fun j => (relatorMask 22).testBit j.val) := by
  change wordEval hA hB (relatorLetters 22) = _
  rw [letters_22, eval_w384]
  exact eval_mask1809.symm

lemma letters_23 : relatorLetters 23 = w395 := by decide +kernel
lemma evaluation_23 : representation hA hB (localRelator hA hB 23) =
    matrixProduct (fun j => (relatorMask 23).testBit j.val) := by
  change wordEval hA hB (relatorLetters 23) = _
  rw [letters_23, eval_w395]
  exact eval_mask272.symm

lemma letters_24 : relatorLetters 24 = w400 := by decide +kernel
lemma evaluation_24 : representation hA hB (localRelator hA hB 24) =
    matrixProduct (fun j => (relatorMask 24).testBit j.val) := by
  change wordEval hA hB (relatorLetters 24) = _
  rw [letters_24, eval_w400]
  exact eval_mask573.symm

lemma letters_25 : relatorLetters 25 = w412 := by decide +kernel
lemma evaluation_25 : representation hA hB (localRelator hA hB 25) =
    matrixProduct (fun j => (relatorMask 25).testBit j.val) := by
  change wordEval hA hB (relatorLetters 25) = _
  rw [letters_25, eval_w412]
  exact eval_mask891.symm

lemma letters_26 : relatorLetters 26 = w423 := by decide +kernel
lemma evaluation_26 : representation hA hB (localRelator hA hB 26) =
    matrixProduct (fun j => (relatorMask 26).testBit j.val) := by
  change wordEval hA hB (relatorLetters 26) = _
  rw [letters_26, eval_w423]
  exact eval_mask1647.symm

lemma letters_27 : relatorLetters 27 = w433 := by decide +kernel
lemma evaluation_27 : representation hA hB (localRelator hA hB 27) =
    matrixProduct (fun j => (relatorMask 27).testBit j.val) := by
  change wordEval hA hB (relatorLetters 27) = _
  rw [letters_27, eval_w433]
  exact eval_mask456.symm

lemma letters_28 : relatorLetters 28 = w449 := by decide +kernel
lemma evaluation_28 : representation hA hB (localRelator hA hB 28) =
    matrixProduct (fun j => (relatorMask 28).testBit j.val) := by
  change wordEval hA hB (relatorLetters 28) = _
  rw [letters_28, eval_w449]
  exact eval_mask809.symm

lemma letters_29 : relatorLetters 29 = w464 := by decide +kernel
lemma evaluation_29 : representation hA hB (localRelator hA hB 29) =
    matrixProduct (fun j => (relatorMask 29).testBit j.val) := by
  change wordEval hA hB (relatorLetters 29) = _
  rw [letters_29, eval_w464]
  exact eval_mask1020.symm

lemma letters_30 : relatorLetters 30 = w481 := by decide +kernel
lemma evaluation_30 : representation hA hB (localRelator hA hB 30) =
    matrixProduct (fun j => (relatorMask 30).testBit j.val) := by
  change wordEval hA hB (relatorLetters 30) = _
  rw [letters_30, eval_w481]
  exact eval_mask1631.symm

lemma letters_31 : relatorLetters 31 = w497 := by decide +kernel
lemma evaluation_31 : representation hA hB (localRelator hA hB 31) =
    matrixProduct (fun j => (relatorMask 31).testBit j.val) := by
  change wordEval hA hB (relatorLetters 31) = _
  rw [letters_31, eval_w497]
  exact eval_mask2005.symm

lemma letters_32 : relatorLetters 32 = w516 := by decide +kernel
lemma evaluation_32 : representation hA hB (localRelator hA hB 32) =
    matrixProduct (fun j => (relatorMask 32).testBit j.val) := by
  change wordEval hA hB (relatorLetters 32) = _
  rw [letters_32, eval_w516]
  exact eval_mask1120.symm

lemma letters_33 : relatorLetters 33 = w531 := by decide +kernel
lemma evaluation_33 : representation hA hB (localRelator hA hB 33) =
    matrixProduct (fun j => (relatorMask 33).testBit j.val) := by
  change wordEval hA hB (relatorLetters 33) = _
  rw [letters_33, eval_w531]
  exact eval_mask319.symm

lemma letters_34 : relatorLetters 34 = w533 := by decide +kernel
lemma evaluation_34 : representation hA hB (localRelator hA hB 34) =
    matrixProduct (fun j => (relatorMask 34).testBit j.val) := by
  change wordEval hA hB (relatorLetters 34) = _
  rw [letters_34, eval_w533]
  exact eval_mask24.symm

lemma letters_35 : relatorLetters 35 = w552 := by decide +kernel
lemma evaluation_35 : representation hA hB (localRelator hA hB 35) =
    matrixProduct (fun j => (relatorMask 35).testBit j.val) := by
  change wordEval hA hB (relatorLetters 35) = _
  rw [letters_35, eval_w552]
  exact eval_mask1556.symm

lemma letters_36 : relatorLetters 36 = w567 := by decide +kernel
lemma evaluation_36 : representation hA hB (localRelator hA hB 36) =
    matrixProduct (fun j => (relatorMask 36).testBit j.val) := by
  change wordEval hA hB (relatorLetters 36) = _
  rw [letters_36, eval_w567]
  exact eval_mask1600.symm

lemma letters_37 : relatorLetters 37 = w582 := by decide +kernel
lemma evaluation_37 : representation hA hB (localRelator hA hB 37) =
    matrixProduct (fun j => (relatorMask 37).testBit j.val) := by
  change wordEval hA hB (relatorLetters 37) = _
  rw [letters_37, eval_w582]
  exact eval_mask926.symm

lemma letters_38 : relatorLetters 38 = w588 := by decide +kernel
lemma evaluation_38 : representation hA hB (localRelator hA hB 38) =
    matrixProduct (fun j => (relatorMask 38).testBit j.val) := by
  change wordEval hA hB (relatorLetters 38) = _
  rw [letters_38, eval_w588]
  exact eval_mask180.symm

lemma letters_39 : relatorLetters 39 = w608 := by decide +kernel
lemma evaluation_39 : representation hA hB (localRelator hA hB 39) =
    matrixProduct (fun j => (relatorMask 39).testBit j.val) := by
  change wordEval hA hB (relatorLetters 39) = _
  rw [letters_39, eval_w608]
  exact eval_mask450.symm

lemma letters_40 : relatorLetters 40 = w627 := by decide +kernel
lemma evaluation_40 : representation hA hB (localRelator hA hB 40) =
    matrixProduct (fun j => (relatorMask 40).testBit j.val) := by
  change wordEval hA hB (relatorLetters 40) = _
  rw [letters_40, eval_w627]
  exact eval_mask1778.symm

lemma letters_41 : relatorLetters 41 = w647 := by decide +kernel
lemma evaluation_41 : representation hA hB (localRelator hA hB 41) =
    matrixProduct (fun j => (relatorMask 41).testBit j.val) := by
  change wordEval hA hB (relatorLetters 41) = _
  rw [letters_41, eval_w647]
  exact eval_mask1340.symm

lemma letters_42 : relatorLetters 42 = w661 := by decide +kernel
lemma evaluation_42 : representation hA hB (localRelator hA hB 42) =
    matrixProduct (fun j => (relatorMask 42).testBit j.val) := by
  change wordEval hA hB (relatorLetters 42) = _
  rw [letters_42, eval_w661]
  exact eval_mask716.symm

lemma letters_43 : relatorLetters 43 = w676 := by decide +kernel
lemma evaluation_43 : representation hA hB (localRelator hA hB 43) =
    matrixProduct (fun j => (relatorMask 43).testBit j.val) := by
  change wordEval hA hB (relatorLetters 43) = _
  rw [letters_43, eval_w676]
  exact eval_mask868.symm

lemma letters_44 : relatorLetters 44 = w697 := by decide +kernel
lemma evaluation_44 : representation hA hB (localRelator hA hB 44) =
    matrixProduct (fun j => (relatorMask 44).testBit j.val) := by
  change wordEval hA hB (relatorLetters 44) = _
  rw [letters_44, eval_w697]
  exact eval_mask390.symm

lemma letters_45 : relatorLetters 45 = w717 := by decide +kernel
lemma evaluation_45 : representation hA hB (localRelator hA hB 45) =
    matrixProduct (fun j => (relatorMask 45).testBit j.val) := by
  change wordEval hA hB (relatorLetters 45) = _
  rw [letters_45, eval_w717]
  exact eval_mask1642.symm

lemma letters_46 : relatorLetters 46 = w738 := by decide +kernel
lemma evaluation_46 : representation hA hB (localRelator hA hB 46) =
    matrixProduct (fun j => (relatorMask 46).testBit j.val) := by
  change wordEval hA hB (relatorLetters 46) = _
  rw [letters_46, eval_w738]
  exact eval_mask1894.symm


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
