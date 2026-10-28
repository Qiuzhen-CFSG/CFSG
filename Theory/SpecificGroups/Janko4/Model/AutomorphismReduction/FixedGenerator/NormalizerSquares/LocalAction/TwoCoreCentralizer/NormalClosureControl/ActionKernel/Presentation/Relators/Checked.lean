module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Evaluations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Masks

/-!
# Certified lifts of the max2 quotient relators

Shared subwords factor the explicit words in `Presentation.Data`. The original
ATLAS max2 matrices and thirteen normal-closure generators are already checked
in `CentralizerReduction`. Each additional product is checked by kernel reduction
of the proved packed arithmetic; Python supplies witnesses only. The resulting
relator lifts are actual words in the relative normal closure, with no local
identification or order assumed. See `Presentation/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

lemma letters_0 : relatorLetters 0 = w62 := by decide +kernel
lemma evaluation_0 : representation (localRelator 0) =
    matrixProduct (relatorMask 0) := by
  change wordEval (relatorLetters 0) = _
  rw [letters_0, eval_w62]
  exact eval_mask0.symm

lemma letters_1 : relatorLetters 1 = w64 := by decide +kernel
lemma evaluation_1 : representation (localRelator 1) =
    matrixProduct (relatorMask 1) := by
  change wordEval (relatorLetters 1) = _
  rw [letters_1, eval_w64]
  exact eval_mask0.symm

lemma letters_2 : relatorLetters 2 = w67 := by decide +kernel
lemma evaluation_2 : representation (localRelator 2) =
    matrixProduct (relatorMask 2) := by
  change wordEval (relatorLetters 2) = _
  rw [letters_2, eval_w67]
  exact eval_mask0.symm

lemma letters_3 : relatorLetters 3 = w73 := by decide +kernel
lemma evaluation_3 : representation (localRelator 3) =
    matrixProduct (relatorMask 3) := by
  change wordEval (relatorLetters 3) = _
  rw [letters_3, eval_w73]
  exact eval_mask3699.symm

lemma letters_4 : relatorLetters 4 = w77 := by decide +kernel
lemma evaluation_4 : representation (localRelator 4) =
    matrixProduct (relatorMask 4) := by
  change wordEval (relatorLetters 4) = _
  rw [letters_4, eval_w77]
  exact eval_mask13.symm

lemma letters_5 : relatorLetters 5 = w83 := by decide +kernel
lemma evaluation_5 : representation (localRelator 5) =
    matrixProduct (relatorMask 5) := by
  change wordEval (relatorLetters 5) = _
  rw [letters_5, eval_w83]
  exact eval_mask2994.symm

lemma letters_6 : relatorLetters 6 = w94 := by decide +kernel
lemma evaluation_6 : representation (localRelator 6) =
    matrixProduct (relatorMask 6) := by
  change wordEval (relatorLetters 6) = _
  rw [letters_6, eval_w94]
  exact eval_mask7610.symm

lemma letters_7 : relatorLetters 7 = w101 := by decide +kernel
lemma evaluation_7 : representation (localRelator 7) =
    matrixProduct (relatorMask 7) := by
  change wordEval (relatorLetters 7) = _
  rw [letters_7, eval_w101]
  exact eval_mask5823.symm

lemma letters_8 : relatorLetters 8 = w110 := by decide +kernel
lemma evaluation_8 : representation (localRelator 8) =
    matrixProduct (relatorMask 8) := by
  change wordEval (relatorLetters 8) = _
  rw [letters_8, eval_w110]
  exact eval_mask7695.symm

lemma letters_9 : relatorLetters 9 = w113 := by decide +kernel
lemma evaluation_9 : representation (localRelator 9) =
    matrixProduct (relatorMask 9) := by
  change wordEval (relatorLetters 9) = _
  rw [letters_9, eval_w113]
  exact eval_mask5717.symm

lemma letters_10 : relatorLetters 10 = w120 := by decide +kernel
lemma evaluation_10 : representation (localRelator 10) =
    matrixProduct (relatorMask 10) := by
  change wordEval (relatorLetters 10) = _
  rw [letters_10, eval_w120]
  exact eval_mask2678.symm

lemma letters_11 : relatorLetters 11 = w130 := by decide +kernel
lemma evaluation_11 : representation (localRelator 11) =
    matrixProduct (relatorMask 11) := by
  change wordEval (relatorLetters 11) = _
  rw [letters_11, eval_w130]
  exact eval_mask4600.symm

lemma letters_12 : relatorLetters 12 = w139 := by decide +kernel
lemma evaluation_12 : representation (localRelator 12) =
    matrixProduct (relatorMask 12) := by
  change wordEval (relatorLetters 12) = _
  rw [letters_12, eval_w139]
  exact eval_mask4241.symm

lemma letters_13 : relatorLetters 13 = w145 := by decide +kernel
lemma evaluation_13 : representation (localRelator 13) =
    matrixProduct (relatorMask 13) := by
  change wordEval (relatorLetters 13) = _
  rw [letters_13, eval_w145]
  exact eval_mask3150.symm

lemma letters_14 : relatorLetters 14 = w152 := by decide +kernel
lemma evaluation_14 : representation (localRelator 14) =
    matrixProduct (relatorMask 14) := by
  change wordEval (relatorLetters 14) = _
  rw [letters_14, eval_w152]
  exact eval_mask5867.symm

lemma letters_15 : relatorLetters 15 = w164 := by decide +kernel
lemma evaluation_15 : representation (localRelator 15) =
    matrixProduct (relatorMask 15) := by
  change wordEval (relatorLetters 15) = _
  rw [letters_15, eval_w164]
  exact eval_mask1673.symm

lemma letters_16 : relatorLetters 16 = w174 := by decide +kernel
lemma evaluation_16 : representation (localRelator 16) =
    matrixProduct (relatorMask 16) := by
  change wordEval (relatorLetters 16) = _
  rw [letters_16, eval_w174]
  exact eval_mask1001.symm

lemma letters_17 : relatorLetters 17 = w186 := by decide +kernel
lemma evaluation_17 : representation (localRelator 17) =
    matrixProduct (relatorMask 17) := by
  change wordEval (relatorLetters 17) = _
  rw [letters_17, eval_w186]
  exact eval_mask7450.symm

lemma letters_18 : relatorLetters 18 = w200 := by decide +kernel
lemma evaluation_18 : representation (localRelator 18) =
    matrixProduct (relatorMask 18) := by
  change wordEval (relatorLetters 18) = _
  rw [letters_18, eval_w200]
  exact eval_mask3967.symm

lemma letters_19 : relatorLetters 19 = w210 := by decide +kernel
lemma evaluation_19 : representation (localRelator 19) =
    matrixProduct (relatorMask 19) := by
  change wordEval (relatorLetters 19) = _
  rw [letters_19, eval_w210]
  exact eval_mask195.symm

lemma letters_20 : relatorLetters 20 = w216 := by decide +kernel
lemma evaluation_20 : representation (localRelator 20) =
    matrixProduct (relatorMask 20) := by
  change wordEval (relatorLetters 20) = _
  rw [letters_20, eval_w216]
  exact eval_mask8110.symm

lemma letters_21 : relatorLetters 21 = w229 := by decide +kernel
lemma evaluation_21 : representation (localRelator 21) =
    matrixProduct (relatorMask 21) := by
  change wordEval (relatorLetters 21) = _
  rw [letters_21, eval_w229]
  exact eval_mask2829.symm

lemma letters_22 : relatorLetters 22 = w242 := by decide +kernel
lemma evaluation_22 : representation (localRelator 22) =
    matrixProduct (relatorMask 22) := by
  change wordEval (relatorLetters 22) = _
  rw [letters_22, eval_w242]
  exact eval_mask6079.symm

lemma letters_23 : relatorLetters 23 = w255 := by decide +kernel
lemma evaluation_23 : representation (localRelator 23) =
    matrixProduct (relatorMask 23) := by
  change wordEval (relatorLetters 23) = _
  rw [letters_23, eval_w255]
  exact eval_mask3182.symm

lemma letters_24 : relatorLetters 24 = w271 := by decide +kernel
lemma evaluation_24 : representation (localRelator 24) =
    matrixProduct (relatorMask 24) := by
  change wordEval (relatorLetters 24) = _
  rw [letters_24, eval_w271]
  exact eval_mask551.symm

lemma letters_25 : relatorLetters 25 = w282 := by decide +kernel
lemma evaluation_25 : representation (localRelator 25) =
    matrixProduct (relatorMask 25) := by
  change wordEval (relatorLetters 25) = _
  rw [letters_25, eval_w282]
  exact eval_mask7004.symm

lemma letters_26 : relatorLetters 26 = w296 := by decide +kernel
lemma evaluation_26 : representation (localRelator 26) =
    matrixProduct (relatorMask 26) := by
  change wordEval (relatorLetters 26) = _
  rw [letters_26, eval_w296]
  exact eval_mask4784.symm

lemma letters_27 : relatorLetters 27 = w306 := by decide +kernel
lemma evaluation_27 : representation (localRelator 27) =
    matrixProduct (relatorMask 27) := by
  change wordEval (relatorLetters 27) = _
  rw [letters_27, eval_w306]
  exact eval_mask2759.symm

lemma letters_28 : relatorLetters 28 = w320 := by decide +kernel
lemma evaluation_28 : representation (localRelator 28) =
    matrixProduct (relatorMask 28) := by
  change wordEval (relatorLetters 28) = _
  rw [letters_28, eval_w320]
  exact eval_mask3550.symm


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
