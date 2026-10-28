module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products00
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products01
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products02
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products03
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products04
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products05
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products06
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products07
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products08
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products09
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products10
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products11
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products12
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products13
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products14
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products15
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products16
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products17
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products18
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products19
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products20
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products21
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Products22
import Mathlib.Tactic.FinCases

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

lemma expand_mask0 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 0 = 1 := by
  have hm (j : Fin 13) : (0 : ℕ).testBit j.val = ![false, false, false, false, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask0 : matrixProduct 0 = decodeRows packedOne := by
  rw [matrixProduct, expand_mask0]
  exact decode_packedOne.symm

lemma expand_mask3699 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3699 = e 0 * (e 1 * (e 4 * (e 5 * (e 6 * (e 9 * (e 10 * (e 11))))))) := by
  have hm (j : Fin 13) : (3699 : ℕ).testBit j.val = ![true, true, false, false, true, true, true, false, false, true, true, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3699 : matrixProduct 3699 = decodeRows r70Rows := by
  rw [matrixProduct, expand_mask3699]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e11Rows))))))) = _
  rw [decoded_product product_321, decoded_product product_322, decoded_product product_323, decoded_product product_324, decoded_product product_325, decoded_product product_326, decoded_product product_327]

lemma expand_mask13 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 13 = e 0 * (e 2 * (e 3)) := by
  have hm (j : Fin 13) : (13 : ℕ).testBit j.val = ![true, false, true, true, false, false, false, false, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask13 : matrixProduct 13 = decodeRows r74Rows := by
  rw [matrixProduct, expand_mask13]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e3Rows)) = _
  rw [decoded_product product_328, decoded_product product_329]

lemma expand_mask2994 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2994 = e 1 * (e 4 * (e 5 * (e 7 * (e 8 * (e 9 * (e 11)))))) := by
  have hm (j : Fin 13) : (2994 : ℕ).testBit j.val = ![false, true, false, false, true, true, false, true, true, true, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2994 : matrixProduct 2994 = decodeRows r80Rows := by
  rw [matrixProduct, expand_mask2994]
  change decodeRows e1Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e11Rows)))))) = _
  rw [decoded_product product_330, decoded_product product_331, decoded_product product_332, decoded_product product_333, decoded_product product_334, decoded_product product_335]

lemma expand_mask7610 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 7610 = e 1 * (e 3 * (e 4 * (e 5 * (e 7 * (e 8 * (e 10 * (e 11 * (e 12)))))))) := by
  have hm (j : Fin 13) : (7610 : ℕ).testBit j.val = ![false, true, false, true, true, true, false, true, true, false, true, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask7610 : matrixProduct 7610 = decodeRows r91Rows := by
  rw [matrixProduct, expand_mask7610]
  change decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e10Rows * (decodeRows e11Rows * (decodeRows e12Rows)))))))) = _
  rw [decoded_product product_336, decoded_product product_337, decoded_product product_338, decoded_product product_339, decoded_product product_340, decoded_product product_341, decoded_product product_342, decoded_product product_343]

lemma expand_mask5823 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 5823 = e 0 * (e 1 * (e 2 * (e 3 * (e 4 * (e 5 * (e 7 * (e 9 * (e 10 * (e 12))))))))) := by
  have hm (j : Fin 13) : (5823 : ℕ).testBit j.val = ![true, true, true, true, true, true, false, true, false, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask5823 : matrixProduct 5823 = decodeRows r98Rows := by
  rw [matrixProduct, expand_mask5823]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e12Rows))))))))) = _
  rw [decoded_product product_344, decoded_product product_345, decoded_product product_346, decoded_product product_347, decoded_product product_348, decoded_product product_349, decoded_product product_350, decoded_product product_351, decoded_product product_352]

lemma expand_mask7695 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 7695 = e 0 * (e 1 * (e 2 * (e 3 * (e 9 * (e 10 * (e 11 * (e 12))))))) := by
  have hm (j : Fin 13) : (7695 : ℕ).testBit j.val = ![true, true, true, true, false, false, false, false, false, true, true, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask7695 : matrixProduct 7695 = decodeRows r107Rows := by
  rw [matrixProduct, expand_mask7695]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e11Rows * (decodeRows e12Rows))))))) = _
  rw [decoded_product product_336, decoded_product product_337, decoded_product product_353, decoded_product product_354, decoded_product product_355, decoded_product product_356, decoded_product product_357]

lemma expand_mask5717 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 5717 = e 0 * (e 2 * (e 4 * (e 6 * (e 9 * (e 10 * (e 12)))))) := by
  have hm (j : Fin 13) : (5717 : ℕ).testBit j.val = ![true, false, true, false, true, false, true, false, false, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask5717 : matrixProduct 5717 = decodeRows r110Rows := by
  rw [matrixProduct, expand_mask5717]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e12Rows)))))) = _
  rw [decoded_product product_344, decoded_product product_345, decoded_product product_358, decoded_product product_359, decoded_product product_360, decoded_product product_361]

lemma expand_mask2678 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2678 = e 1 * (e 2 * (e 4 * (e 5 * (e 6 * (e 9 * (e 11)))))) := by
  have hm (j : Fin 13) : (2678 : ℕ).testBit j.val = ![false, true, true, false, true, true, true, false, false, true, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2678 : matrixProduct 2678 = decodeRows r117Rows := by
  rw [matrixProduct, expand_mask2678]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e11Rows)))))) = _
  rw [decoded_product product_330, decoded_product product_362, decoded_product product_363, decoded_product product_364, decoded_product product_365, decoded_product product_366]

lemma expand_mask4600 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 4600 = e 3 * (e 4 * (e 5 * (e 6 * (e 7 * (e 8 * (e 12)))))) := by
  have hm (j : Fin 13) : (4600 : ℕ).testBit j.val = ![false, false, false, true, true, true, true, true, true, false, false, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask4600 : matrixProduct 4600 = decodeRows r127Rows := by
  rw [matrixProduct, expand_mask4600]
  change decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e12Rows)))))) = _
  rw [decoded_product product_367, decoded_product product_368, decoded_product product_369, decoded_product product_370, decoded_product product_371, decoded_product product_372]

lemma expand_mask4241 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 4241 = e 0 * (e 4 * (e 7 * (e 12))) := by
  have hm (j : Fin 13) : (4241 : ℕ).testBit j.val = ![true, false, false, false, true, false, false, true, false, false, false, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask4241 : matrixProduct 4241 = decodeRows r136Rows := by
  rw [matrixProduct, expand_mask4241]
  change decodeRows e0Rows * (decodeRows e4Rows * (decodeRows e7Rows * (decodeRows e12Rows))) = _
  rw [decoded_product product_373, decoded_product product_374, decoded_product product_375]

lemma expand_mask3150 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3150 = e 1 * (e 2 * (e 3 * (e 6 * (e 10 * (e 11))))) := by
  have hm (j : Fin 13) : (3150 : ℕ).testBit j.val = ![false, true, true, true, false, false, true, false, false, false, true, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3150 : matrixProduct 3150 = decodeRows r142Rows := by
  rw [matrixProduct, expand_mask3150]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e6Rows * (decodeRows e10Rows * (decodeRows e11Rows))))) = _
  rw [decoded_product product_321, decoded_product product_376, decoded_product product_377, decoded_product product_378, decoded_product product_379]

lemma expand_mask5867 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 5867 = e 0 * (e 1 * (e 3 * (e 5 * (e 6 * (e 7 * (e 9 * (e 10 * (e 12)))))))) := by
  have hm (j : Fin 13) : (5867 : ℕ).testBit j.val = ![true, true, false, true, false, true, true, true, false, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask5867 : matrixProduct 5867 = decodeRows r149Rows := by
  rw [matrixProduct, expand_mask5867]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e12Rows)))))))) = _
  rw [decoded_product product_344, decoded_product product_345, decoded_product product_346, decoded_product product_380, decoded_product product_381, decoded_product product_382, decoded_product product_383, decoded_product product_384]

lemma expand_mask1673 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 1673 = e 0 * (e 3 * (e 7 * (e 9 * (e 10)))) := by
  have hm (j : Fin 13) : (1673 : ℕ).testBit j.val = ![true, false, false, true, false, false, false, true, false, true, true, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask1673 : matrixProduct 1673 = decodeRows r161Rows := by
  rw [matrixProduct, expand_mask1673]
  change decodeRows e0Rows * (decodeRows e3Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e10Rows)))) = _
  rw [decoded_product product_385, decoded_product product_386, decoded_product product_387, decoded_product product_388]

lemma expand_mask1001 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 1001 = e 0 * (e 3 * (e 5 * (e 6 * (e 7 * (e 8 * (e 9)))))) := by
  have hm (j : Fin 13) : (1001 : ℕ).testBit j.val = ![true, false, false, true, false, true, true, true, true, true, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask1001 : matrixProduct 1001 = decodeRows r171Rows := by
  rw [matrixProduct, expand_mask1001]
  change decodeRows e0Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows)))))) = _
  rw [decoded_product product_389, decoded_product product_390, decoded_product product_391, decoded_product product_392, decoded_product product_393, decoded_product product_394]

lemma expand_mask7450 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 7450 = e 1 * (e 3 * (e 4 * (e 8 * (e 10 * (e 11 * (e 12)))))) := by
  have hm (j : Fin 13) : (7450 : ℕ).testBit j.val = ![false, true, false, true, true, false, false, false, true, false, true, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask7450 : matrixProduct 7450 = decodeRows r183Rows := by
  rw [matrixProduct, expand_mask7450]
  change decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e8Rows * (decodeRows e10Rows * (decodeRows e11Rows * (decodeRows e12Rows)))))) = _
  rw [decoded_product product_336, decoded_product product_337, decoded_product product_338, decoded_product product_395, decoded_product product_396, decoded_product product_397]

lemma expand_mask3967 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3967 = e 0 * (e 1 * (e 2 * (e 3 * (e 4 * (e 5 * (e 6 * (e 8 * (e 9 * (e 10 * (e 11)))))))))) := by
  have hm (j : Fin 13) : (3967 : ℕ).testBit j.val = ![true, true, true, true, true, true, true, false, true, true, true, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3967 : matrixProduct 3967 = decodeRows r197Rows := by
  rw [matrixProduct, expand_mask3967]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e11Rows)))))))))) = _
  rw [decoded_product product_321, decoded_product product_322, decoded_product product_398, decoded_product product_399, decoded_product product_400, decoded_product product_401, decoded_product product_402, decoded_product product_403, decoded_product product_404, decoded_product product_405]

lemma expand_mask195 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 195 = e 0 * (e 1 * (e 6 * (e 7))) := by
  have hm (j : Fin 13) : (195 : ℕ).testBit j.val = ![true, true, false, false, false, false, true, true, false, false, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask195 : matrixProduct 195 = decodeRows r207Rows := by
  rw [matrixProduct, expand_mask195]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e6Rows * (decodeRows e7Rows))) = _
  rw [decoded_product product_406, decoded_product product_407, decoded_product product_408]

lemma expand_mask8110 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 8110 = e 1 * (e 2 * (e 3 * (e 5 * (e 7 * (e 8 * (e 9 * (e 10 * (e 11 * (e 12))))))))) := by
  have hm (j : Fin 13) : (8110 : ℕ).testBit j.val = ![false, true, true, true, false, true, false, true, true, true, true, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask8110 : matrixProduct 8110 = decodeRows r213Rows := by
  rw [matrixProduct, expand_mask8110]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e11Rows * (decodeRows e12Rows))))))))) = _
  rw [decoded_product product_336, decoded_product product_337, decoded_product product_353, decoded_product product_409, decoded_product product_410, decoded_product product_411, decoded_product product_412, decoded_product product_413, decoded_product product_414]

lemma expand_mask2829 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2829 = e 0 * (e 2 * (e 3 * (e 8 * (e 9 * (e 11))))) := by
  have hm (j : Fin 13) : (2829 : ℕ).testBit j.val = ![true, false, true, true, false, false, false, false, true, true, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2829 : matrixProduct 2829 = decodeRows r226Rows := by
  rw [matrixProduct, expand_mask2829]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e11Rows))))) = _
  rw [decoded_product product_330, decoded_product product_331, decoded_product product_415, decoded_product product_416, decoded_product product_417]

lemma expand_mask6079 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 6079 = e 0 * (e 1 * (e 2 * (e 3 * (e 4 * (e 5 * (e 7 * (e 8 * (e 9 * (e 10 * (e 12)))))))))) := by
  have hm (j : Fin 13) : (6079 : ℕ).testBit j.val = ![true, true, true, true, true, true, false, true, true, true, true, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask6079 : matrixProduct 6079 = decodeRows r239Rows := by
  rw [matrixProduct, expand_mask6079]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows * (decodeRows e12Rows)))))))))) = _
  rw [decoded_product product_344, decoded_product product_345, decoded_product product_418, decoded_product product_419, decoded_product product_420, decoded_product product_421, decoded_product product_422, decoded_product product_423, decoded_product product_424, decoded_product product_425]

lemma expand_mask3182 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3182 = e 1 * (e 2 * (e 3 * (e 5 * (e 6 * (e 10 * (e 11)))))) := by
  have hm (j : Fin 13) : (3182 : ℕ).testBit j.val = ![false, true, true, true, false, true, true, false, false, false, true, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3182 : matrixProduct 3182 = decodeRows r252Rows := by
  rw [matrixProduct, expand_mask3182]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e10Rows * (decodeRows e11Rows)))))) = _
  rw [decoded_product product_321, decoded_product product_376, decoded_product product_426, decoded_product product_427, decoded_product product_428, decoded_product product_429]

lemma expand_mask551 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 551 = e 0 * (e 1 * (e 2 * (e 5 * (e 9)))) := by
  have hm (j : Fin 13) : (551 : ℕ).testBit j.val = ![true, true, true, false, false, true, false, false, false, true, false, false, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask551 : matrixProduct 551 = decodeRows r268Rows := by
  rw [matrixProduct, expand_mask551]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e5Rows * (decodeRows e9Rows)))) = _
  rw [decoded_product product_430, decoded_product product_431, decoded_product product_432, decoded_product product_433]

lemma expand_mask7004 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 7004 = e 2 * (e 3 * (e 4 * (e 6 * (e 8 * (e 9 * (e 11 * (e 12))))))) := by
  have hm (j : Fin 13) : (7004 : ℕ).testBit j.val = ![false, false, true, true, true, false, true, false, true, true, false, true, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask7004 : matrixProduct 7004 = decodeRows r279Rows := by
  rw [matrixProduct, expand_mask7004]
  change decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e11Rows * (decodeRows e12Rows))))))) = _
  rw [decoded_product product_336, decoded_product product_434, decoded_product product_435, decoded_product product_436, decoded_product product_437, decoded_product product_438, decoded_product product_439]

lemma expand_mask4784 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 4784 = e 4 * (e 5 * (e 7 * (e 9 * (e 12)))) := by
  have hm (j : Fin 13) : (4784 : ℕ).testBit j.val = ![false, false, false, false, true, true, false, true, false, true, false, false, true] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask4784 : matrixProduct 4784 = decodeRows r293Rows := by
  rw [matrixProduct, expand_mask4784]
  change decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e12Rows)))) = _
  rw [decoded_product product_440, decoded_product product_441, decoded_product product_442, decoded_product product_443]

lemma expand_mask2759 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 2759 = e 0 * (e 1 * (e 2 * (e 6 * (e 7 * (e 9 * (e 11)))))) := by
  have hm (j : Fin 13) : (2759 : ℕ).testBit j.val = ![true, true, true, false, false, false, true, true, false, true, false, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask2759 : matrixProduct 2759 = decodeRows r303Rows := by
  rw [matrixProduct, expand_mask2759]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e11Rows)))))) = _
  rw [decoded_product product_330, decoded_product product_444, decoded_product product_445, decoded_product product_446, decoded_product product_447, decoded_product product_448]

lemma expand_mask3550 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    maskProduct e 3550 = e 1 * (e 2 * (e 3 * (e 4 * (e 6 * (e 7 * (e 8 * (e 10 * (e 11)))))))) := by
  have hm (j : Fin 13) : (3550 : ℕ).testBit j.val = ![false, true, true, true, true, false, true, true, true, false, true, true, false] j := by
    fin_cases j <;> decide +kernel
  simp only [maskProduct, hm]
  simp [List.ofFn_succ]

lemma eval_mask3550 : matrixProduct 3550 = decodeRows r317Rows := by
  rw [matrixProduct, expand_mask3550]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e10Rows * (decodeRows e11Rows)))))))) = _
  rw [decoded_product product_321, decoded_product product_449, decoded_product product_450, decoded_product product_451, decoded_product product_452, decoded_product product_453, decoded_product product_454, decoded_product product_455]


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
