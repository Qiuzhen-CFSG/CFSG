module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products00
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products01
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products02
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products03
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products04
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products05
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products06
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products07
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products08
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products09
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products10
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products11
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products12
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products13
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products14
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products15
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products16
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products17
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products18
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products19
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products20
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products21
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products22
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products23
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products24
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products25
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products26
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products27
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products28
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products29
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products30
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products31
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products32
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products33
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Products34

import Mathlib.Tactic.FinCases

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

lemma expand_mask0 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (0 : ℕ).testBit j.val) = 1 := by
  have h : (fun j : Fin 11 => (0 : ℕ).testBit j.val) = ![false, false, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask0 : matrixProduct (fun j => (0 : ℕ).testBit j.val) =
    decodeRows packedOne := by
  rw [matrixProduct, expand_mask0]
  exact decode_packedOne.symm

lemma expand_mask2 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (2 : ℕ).testBit j.val) = e 1 := by
  have h : (fun j : Fin 11 => (2 : ℕ).testBit j.val) = ![false, true, false, false, false, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask2 : matrixProduct (fun j => (2 : ℕ).testBit j.val) =
    decodeRows e1Rows := by
  rw [matrixProduct, expand_mask2]
  rfl

lemma expand_mask1348 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1348 : ℕ).testBit j.val) = e 2 * (e 6 * (e 8 * (e 10))) := by
  have h : (fun j : Fin 11 => (1348 : ℕ).testBit j.val) = ![false, false, true, false, false, false, true, false, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1348 : matrixProduct (fun j => (1348 : ℕ).testBit j.val) =
    decodeRows r194Rows := by
  rw [matrixProduct, expand_mask1348]
  change decodeRows e2Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e10Rows))) = _
  rw [decoded_product product_739, decoded_product product_740, decoded_product product_741]

lemma expand_mask1018 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1018 : ℕ).testBit j.val) = e 1 * (e 3 * (e 4 * (e 5 * (e 6 * (e 7 * (e 8 * (e 9))))))) := by
  have h : (fun j : Fin 11 => (1018 : ℕ).testBit j.val) = ![false, true, false, true, true, true, true, true, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1018 : matrixProduct (fun j => (1018 : ℕ).testBit j.val) =
    decodeRows r201Rows := by
  rw [matrixProduct, expand_mask1018]
  change decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows))))))) = _
  rw [decoded_product product_742, decoded_product product_743, decoded_product product_744, decoded_product product_745, decoded_product product_746, decoded_product product_747, decoded_product product_748]

lemma expand_mask1366 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1366 : ℕ).testBit j.val) = e 1 * (e 2 * (e 4 * (e 6 * (e 8 * (e 10))))) := by
  have h : (fun j : Fin 11 => (1366 : ℕ).testBit j.val) = ![false, true, true, false, true, false, true, false, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1366 : matrixProduct (fun j => (1366 : ℕ).testBit j.val) =
    decodeRows r209Rows := by
  rw [matrixProduct, expand_mask1366]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e10Rows))))) = _
  rw [decoded_product product_739, decoded_product product_740, decoded_product product_749, decoded_product product_750, decoded_product product_751]

lemma expand_mask1485 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1485 : ℕ).testBit j.val) = e 0 * (e 2 * (e 3 * (e 6 * (e 7 * (e 8 * (e 10)))))) := by
  have h : (fun j : Fin 11 => (1485 : ℕ).testBit j.val) = ![true, false, true, true, false, false, true, true, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1485 : matrixProduct (fun j => (1485 : ℕ).testBit j.val) =
    decodeRows r213Rows := by
  rw [matrixProduct, expand_mask1485]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e10Rows)))))) = _
  rw [decoded_product product_739, decoded_product product_752, decoded_product product_753, decoded_product product_754, decoded_product product_755, decoded_product product_756]

lemma expand_mask1166 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1166 : ℕ).testBit j.val) = e 1 * (e 2 * (e 3 * (e 7 * (e 10)))) := by
  have h : (fun j : Fin 11 => (1166 : ℕ).testBit j.val) = ![false, true, true, true, false, false, false, true, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1166 : matrixProduct (fun j => (1166 : ℕ).testBit j.val) =
    decodeRows r223Rows := by
  rw [matrixProduct, expand_mask1166]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e7Rows * (decodeRows e10Rows)))) = _
  rw [decoded_product product_757, decoded_product product_758, decoded_product product_759, decoded_product product_760]

lemma expand_mask784 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (784 : ℕ).testBit j.val) = e 4 * (e 8 * (e 9)) := by
  have h : (fun j : Fin 11 => (784 : ℕ).testBit j.val) = ![false, false, false, false, true, false, false, false, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask784 : matrixProduct (fun j => (784 : ℕ).testBit j.val) =
    decodeRows r225Rows := by
  rw [matrixProduct, expand_mask784]
  change decodeRows e4Rows * (decodeRows e8Rows * (decodeRows e9Rows)) = _
  rw [decoded_product product_742, decoded_product product_761]

lemma expand_mask901 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (901 : ℕ).testBit j.val) = e 0 * (e 2 * (e 7 * (e 8 * (e 9)))) := by
  have h : (fun j : Fin 11 => (901 : ℕ).testBit j.val) = ![true, false, true, false, false, false, false, true, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask901 : matrixProduct (fun j => (901 : ℕ).testBit j.val) =
    decodeRows r233Rows := by
  rw [matrixProduct, expand_mask901]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows)))) = _
  rw [decoded_product product_742, decoded_product product_743, decoded_product product_762, decoded_product product_763]

lemma expand_mask1301 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1301 : ℕ).testBit j.val) = e 0 * (e 2 * (e 4 * (e 8 * (e 10)))) := by
  have h : (fun j : Fin 11 => (1301 : ℕ).testBit j.val) = ![true, false, true, false, true, false, false, false, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1301 : matrixProduct (fun j => (1301 : ℕ).testBit j.val) =
    decodeRows r241Rows := by
  rw [matrixProduct, expand_mask1301]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e8Rows * (decodeRows e10Rows)))) = _
  rw [decoded_product product_739, decoded_product product_764, decoded_product product_765, decoded_product product_766]

lemma expand_mask1388 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1388 : ℕ).testBit j.val) = e 2 * (e 3 * (e 5 * (e 6 * (e 8 * (e 10))))) := by
  have h : (fun j : Fin 11 => (1388 : ℕ).testBit j.val) = ![false, false, true, true, false, true, true, false, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1388 : matrixProduct (fun j => (1388 : ℕ).testBit j.val) =
    decodeRows r251Rows := by
  rw [matrixProduct, expand_mask1388]
  change decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e10Rows))))) = _
  rw [decoded_product product_739, decoded_product product_740, decoded_product product_767, decoded_product product_768, decoded_product product_769]

lemma expand_mask1154 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1154 : ℕ).testBit j.val) = e 1 * (e 7 * (e 10)) := by
  have h : (fun j : Fin 11 => (1154 : ℕ).testBit j.val) = ![false, true, false, false, false, false, false, true, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1154 : matrixProduct (fun j => (1154 : ℕ).testBit j.val) =
    decodeRows r260Rows := by
  rw [matrixProduct, expand_mask1154]
  change decodeRows e1Rows * (decodeRows e7Rows * (decodeRows e10Rows)) = _
  rw [decoded_product product_757, decoded_product product_770]

lemma expand_mask1105 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1105 : ℕ).testBit j.val) = e 0 * (e 4 * (e 6 * (e 10))) := by
  have h : (fun j : Fin 11 => (1105 : ℕ).testBit j.val) = ![true, false, false, false, true, false, true, false, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1105 : matrixProduct (fun j => (1105 : ℕ).testBit j.val) =
    decodeRows r274Rows := by
  rw [matrixProduct, expand_mask1105]
  change decodeRows e0Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e10Rows))) = _
  rw [decoded_product product_771, decoded_product product_772, decoded_product product_773]

lemma expand_mask411 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (411 : ℕ).testBit j.val) = e 0 * (e 1 * (e 3 * (e 4 * (e 7 * (e 8))))) := by
  have h : (fun j : Fin 11 => (411 : ℕ).testBit j.val) = ![true, true, false, true, true, false, false, true, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask411 : matrixProduct (fun j => (411 : ℕ).testBit j.val) =
    decodeRows r286Rows := by
  rw [matrixProduct, expand_mask411]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e7Rows * (decodeRows e8Rows))))) = _
  rw [decoded_product product_774, decoded_product product_775, decoded_product product_776, decoded_product product_777, decoded_product product_778]

lemma expand_mask1969 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1969 : ℕ).testBit j.val) = e 0 * (e 4 * (e 5 * (e 7 * (e 8 * (e 9 * (e 10)))))) := by
  have h : (fun j : Fin 11 => (1969 : ℕ).testBit j.val) = ![true, false, false, false, true, true, false, true, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1969 : matrixProduct (fun j => (1969 : ℕ).testBit j.val) =
    decodeRows r304Rows := by
  rw [matrixProduct, expand_mask1969]
  change decodeRows e0Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows)))))) = _
  rw [decoded_product product_779, decoded_product product_780, decoded_product product_781, decoded_product product_782, decoded_product product_783, decoded_product product_784]

lemma expand_mask1184 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1184 : ℕ).testBit j.val) = e 5 * (e 7 * (e 10)) := by
  have h : (fun j : Fin 11 => (1184 : ℕ).testBit j.val) = ![false, false, false, false, false, true, false, true, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1184 : matrixProduct (fun j => (1184 : ℕ).testBit j.val) =
    decodeRows r319Rows := by
  rw [matrixProduct, expand_mask1184]
  change decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e10Rows)) = _
  rw [decoded_product product_757, decoded_product product_785]

lemma expand_mask1991 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1991 : ℕ).testBit j.val) = e 0 * (e 1 * (e 2 * (e 6 * (e 7 * (e 8 * (e 9 * (e 10))))))) := by
  have h : (fun j : Fin 11 => (1991 : ℕ).testBit j.val) = ![true, true, true, false, false, false, true, true, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1991 : matrixProduct (fun j => (1991 : ℕ).testBit j.val) =
    decodeRows r332Rows := by
  rw [matrixProduct, expand_mask1991]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows))))))) = _
  rw [decoded_product product_779, decoded_product product_780, decoded_product product_781, decoded_product product_786, decoded_product product_787, decoded_product product_788, decoded_product product_789]

lemma expand_mask1465 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1465 : ℕ).testBit j.val) = e 0 * (e 3 * (e 4 * (e 5 * (e 7 * (e 8 * (e 10)))))) := by
  have h : (fun j : Fin 11 => (1465 : ℕ).testBit j.val) = ![true, false, false, true, true, true, false, true, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1465 : matrixProduct (fun j => (1465 : ℕ).testBit j.val) =
    decodeRows r341Rows := by
  rw [matrixProduct, expand_mask1465]
  change decodeRows e0Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e10Rows)))))) = _
  rw [decoded_product product_739, decoded_product product_752, decoded_product product_790, decoded_product product_791, decoded_product product_792, decoded_product product_793]

lemma expand_mask576 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (576 : ℕ).testBit j.val) = e 6 * (e 9) := by
  have h : (fun j : Fin 11 => (576 : ℕ).testBit j.val) = ![false, false, false, false, false, false, true, false, false, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask576 : matrixProduct (fun j => (576 : ℕ).testBit j.val) =
    decodeRows r353Rows := by
  rw [matrixProduct, expand_mask576]
  change decodeRows e6Rows * (decodeRows e9Rows) = _
  rw [decoded_product product_794]

lemma expand_mask1625 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1625 : ℕ).testBit j.val) = e 0 * (e 3 * (e 4 * (e 6 * (e 9 * (e 10))))) := by
  have h : (fun j : Fin 11 => (1625 : ℕ).testBit j.val) = ![true, false, false, true, true, false, true, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1625 : matrixProduct (fun j => (1625 : ℕ).testBit j.val) =
    decodeRows r363Rows := by
  rw [matrixProduct, expand_mask1625]
  change decodeRows e0Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows))))) = _
  rw [decoded_product product_779, decoded_product product_795, decoded_product product_796, decoded_product product_797, decoded_product product_798]

lemma expand_mask1809 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1809 : ℕ).testBit j.val) = e 0 * (e 4 * (e 8 * (e 9 * (e 10)))) := by
  have h : (fun j : Fin 11 => (1809 : ℕ).testBit j.val) = ![true, false, false, false, true, false, false, false, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1809 : matrixProduct (fun j => (1809 : ℕ).testBit j.val) =
    decodeRows r380Rows := by
  rw [matrixProduct, expand_mask1809]
  change decodeRows e0Rows * (decodeRows e4Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows)))) = _
  rw [decoded_product product_779, decoded_product product_780, decoded_product product_799, decoded_product product_800]

lemma expand_mask272 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (272 : ℕ).testBit j.val) = e 4 * (e 8) := by
  have h : (fun j : Fin 11 => (272 : ℕ).testBit j.val) = ![false, false, false, false, true, false, false, false, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask272 : matrixProduct (fun j => (272 : ℕ).testBit j.val) =
    decodeRows r391Rows := by
  rw [matrixProduct, expand_mask272]
  change decodeRows e4Rows * (decodeRows e8Rows) = _
  rw [decoded_product product_801]

lemma expand_mask573 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (573 : ℕ).testBit j.val) = e 0 * (e 2 * (e 3 * (e 4 * (e 5 * (e 9))))) := by
  have h : (fun j : Fin 11 => (573 : ℕ).testBit j.val) = ![true, false, true, true, true, true, false, false, false, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask573 : matrixProduct (fun j => (573 : ℕ).testBit j.val) =
    decodeRows r396Rows := by
  rw [matrixProduct, expand_mask573]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e9Rows))))) = _
  rw [decoded_product product_802, decoded_product product_803, decoded_product product_804, decoded_product product_805, decoded_product product_806]

lemma expand_mask891 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (891 : ℕ).testBit j.val) = e 0 * (e 1 * (e 3 * (e 4 * (e 5 * (e 6 * (e 8 * (e 9))))))) := by
  have h : (fun j : Fin 11 => (891 : ℕ).testBit j.val) = ![true, true, false, true, true, true, true, false, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask891 : matrixProduct (fun j => (891 : ℕ).testBit j.val) =
    decodeRows r408Rows := by
  rw [matrixProduct, expand_mask891]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e9Rows))))))) = _
  rw [decoded_product product_742, decoded_product product_807, decoded_product product_808, decoded_product product_809, decoded_product product_810, decoded_product product_811, decoded_product product_812]

lemma expand_mask1647 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1647 : ℕ).testBit j.val) = e 0 * (e 1 * (e 2 * (e 3 * (e 5 * (e 6 * (e 9 * (e 10))))))) := by
  have h : (fun j : Fin 11 => (1647 : ℕ).testBit j.val) = ![true, true, true, true, false, true, true, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1647 : matrixProduct (fun j => (1647 : ℕ).testBit j.val) =
    decodeRows r419Rows := by
  rw [matrixProduct, expand_mask1647]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows))))))) = _
  rw [decoded_product product_779, decoded_product product_795, decoded_product product_813, decoded_product product_814, decoded_product product_815, decoded_product product_816, decoded_product product_817]

lemma expand_mask456 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (456 : ℕ).testBit j.val) = e 3 * (e 6 * (e 7 * (e 8))) := by
  have h : (fun j : Fin 11 => (456 : ℕ).testBit j.val) = ![false, false, false, true, false, false, true, true, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask456 : matrixProduct (fun j => (456 : ℕ).testBit j.val) =
    decodeRows r429Rows := by
  rw [matrixProduct, expand_mask456]
  change decodeRows e3Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows))) = _
  rw [decoded_product product_774, decoded_product product_818, decoded_product product_819]

lemma expand_mask809 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (809 : ℕ).testBit j.val) = e 0 * (e 3 * (e 5 * (e 8 * (e 9)))) := by
  have h : (fun j : Fin 11 => (809 : ℕ).testBit j.val) = ![true, false, false, true, false, true, false, false, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask809 : matrixProduct (fun j => (809 : ℕ).testBit j.val) =
    decodeRows r445Rows := by
  rw [matrixProduct, expand_mask809]
  change decodeRows e0Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e8Rows * (decodeRows e9Rows)))) = _
  rw [decoded_product product_742, decoded_product product_820, decoded_product product_821, decoded_product product_822]

lemma expand_mask1020 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1020 : ℕ).testBit j.val) = e 2 * (e 3 * (e 4 * (e 5 * (e 6 * (e 7 * (e 8 * (e 9))))))) := by
  have h : (fun j : Fin 11 => (1020 : ℕ).testBit j.val) = ![false, false, true, true, true, true, true, true, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1020 : matrixProduct (fun j => (1020 : ℕ).testBit j.val) =
    decodeRows r460Rows := by
  rw [matrixProduct, expand_mask1020]
  change decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows))))))) = _
  rw [decoded_product product_742, decoded_product product_743, decoded_product product_744, decoded_product product_745, decoded_product product_746, decoded_product product_747, decoded_product product_823]

lemma expand_mask1631 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1631 : ℕ).testBit j.val) = e 0 * (e 1 * (e 2 * (e 3 * (e 4 * (e 6 * (e 9 * (e 10))))))) := by
  have h : (fun j : Fin 11 => (1631 : ℕ).testBit j.val) = ![true, true, true, true, true, false, true, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1631 : matrixProduct (fun j => (1631 : ℕ).testBit j.val) =
    decodeRows r477Rows := by
  rw [matrixProduct, expand_mask1631]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows))))))) = _
  rw [decoded_product product_779, decoded_product product_795, decoded_product product_796, decoded_product product_797, decoded_product product_824, decoded_product product_825, decoded_product product_826]

lemma expand_mask2005 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (2005 : ℕ).testBit j.val) = e 0 * (e 2 * (e 4 * (e 6 * (e 7 * (e 8 * (e 9 * (e 10))))))) := by
  have h : (fun j : Fin 11 => (2005 : ℕ).testBit j.val) = ![true, false, true, false, true, false, true, true, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask2005 : matrixProduct (fun j => (2005 : ℕ).testBit j.val) =
    decodeRows r493Rows := by
  rw [matrixProduct, expand_mask2005]
  change decodeRows e0Rows * (decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows))))))) = _
  rw [decoded_product product_779, decoded_product product_780, decoded_product product_781, decoded_product product_786, decoded_product product_827, decoded_product product_828, decoded_product product_829]

lemma expand_mask1120 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1120 : ℕ).testBit j.val) = e 5 * (e 6 * (e 10)) := by
  have h : (fun j : Fin 11 => (1120 : ℕ).testBit j.val) = ![false, false, false, false, false, true, true, false, false, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1120 : matrixProduct (fun j => (1120 : ℕ).testBit j.val) =
    decodeRows r512Rows := by
  rw [matrixProduct, expand_mask1120]
  change decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e10Rows)) = _
  rw [decoded_product product_771, decoded_product product_830]

lemma expand_mask319 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (319 : ℕ).testBit j.val) = e 0 * (e 1 * (e 2 * (e 3 * (e 4 * (e 5 * (e 8)))))) := by
  have h : (fun j : Fin 11 => (319 : ℕ).testBit j.val) = ![true, true, true, true, true, true, false, false, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask319 : matrixProduct (fun j => (319 : ℕ).testBit j.val) =
    decodeRows r527Rows := by
  rw [matrixProduct, expand_mask319]
  change decodeRows e0Rows * (decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e8Rows)))))) = _
  rw [decoded_product product_831, decoded_product product_832, decoded_product product_833, decoded_product product_834, decoded_product product_835, decoded_product product_836]

lemma expand_mask24 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (24 : ℕ).testBit j.val) = e 3 * (e 4) := by
  have h : (fun j : Fin 11 => (24 : ℕ).testBit j.val) = ![false, false, false, true, true, false, false, false, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask24 : matrixProduct (fun j => (24 : ℕ).testBit j.val) =
    decodeRows r529Rows := by
  rw [matrixProduct, expand_mask24]
  change decodeRows e3Rows * (decodeRows e4Rows) = _
  rw [decoded_product product_837]

lemma expand_mask1556 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1556 : ℕ).testBit j.val) = e 2 * (e 4 * (e 9 * (e 10))) := by
  have h : (fun j : Fin 11 => (1556 : ℕ).testBit j.val) = ![false, false, true, false, true, false, false, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1556 : matrixProduct (fun j => (1556 : ℕ).testBit j.val) =
    decodeRows r548Rows := by
  rw [matrixProduct, expand_mask1556]
  change decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e9Rows * (decodeRows e10Rows))) = _
  rw [decoded_product product_779, decoded_product product_838, decoded_product product_839]

lemma expand_mask1600 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1600 : ℕ).testBit j.val) = e 6 * (e 9 * (e 10)) := by
  have h : (fun j : Fin 11 => (1600 : ℕ).testBit j.val) = ![false, false, false, false, false, false, true, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1600 : matrixProduct (fun j => (1600 : ℕ).testBit j.val) =
    decodeRows r563Rows := by
  rw [matrixProduct, expand_mask1600]
  change decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows)) = _
  rw [decoded_product product_779, decoded_product product_795]

lemma expand_mask926 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (926 : ℕ).testBit j.val) = e 1 * (e 2 * (e 3 * (e 4 * (e 7 * (e 8 * (e 9)))))) := by
  have h : (fun j : Fin 11 => (926 : ℕ).testBit j.val) = ![false, true, true, true, true, false, false, true, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask926 : matrixProduct (fun j => (926 : ℕ).testBit j.val) =
    decodeRows r578Rows := by
  rw [matrixProduct, expand_mask926]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e7Rows * (decodeRows e8Rows * (decodeRows e9Rows)))))) = _
  rw [decoded_product product_742, decoded_product product_743, decoded_product product_840, decoded_product product_841, decoded_product product_842, decoded_product product_843]

lemma expand_mask180 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (180 : ℕ).testBit j.val) = e 2 * (e 4 * (e 5 * (e 7))) := by
  have h : (fun j : Fin 11 => (180 : ℕ).testBit j.val) = ![false, false, true, false, true, true, false, true, false, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask180 : matrixProduct (fun j => (180 : ℕ).testBit j.val) =
    decodeRows r584Rows := by
  rw [matrixProduct, expand_mask180]
  change decodeRows e2Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e7Rows))) = _
  rw [decoded_product product_844, decoded_product product_845, decoded_product product_846]

lemma expand_mask450 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (450 : ℕ).testBit j.val) = e 1 * (e 6 * (e 7 * (e 8))) := by
  have h : (fun j : Fin 11 => (450 : ℕ).testBit j.val) = ![false, true, false, false, false, false, true, true, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask450 : matrixProduct (fun j => (450 : ℕ).testBit j.val) =
    decodeRows r604Rows := by
  rw [matrixProduct, expand_mask450]
  change decodeRows e1Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e8Rows))) = _
  rw [decoded_product product_774, decoded_product product_818, decoded_product product_847]

lemma expand_mask1778 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1778 : ℕ).testBit j.val) = e 1 * (e 4 * (e 5 * (e 6 * (e 7 * (e 9 * (e 10)))))) := by
  have h : (fun j : Fin 11 => (1778 : ℕ).testBit j.val) = ![false, true, false, false, true, true, true, true, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1778 : matrixProduct (fun j => (1778 : ℕ).testBit j.val) =
    decodeRows r623Rows := by
  rw [matrixProduct, expand_mask1778]
  change decodeRows e1Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e9Rows * (decodeRows e10Rows)))))) = _
  rw [decoded_product product_779, decoded_product product_848, decoded_product product_849, decoded_product product_850, decoded_product product_851, decoded_product product_852]

lemma expand_mask1340 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1340 : ℕ).testBit j.val) = e 2 * (e 3 * (e 4 * (e 5 * (e 8 * (e 10))))) := by
  have h : (fun j : Fin 11 => (1340 : ℕ).testBit j.val) = ![false, false, true, true, true, true, false, false, true, false, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1340 : matrixProduct (fun j => (1340 : ℕ).testBit j.val) =
    decodeRows r643Rows := by
  rw [matrixProduct, expand_mask1340]
  change decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e4Rows * (decodeRows e5Rows * (decodeRows e8Rows * (decodeRows e10Rows))))) = _
  rw [decoded_product product_739, decoded_product product_853, decoded_product product_854, decoded_product product_855, decoded_product product_856]

lemma expand_mask716 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (716 : ℕ).testBit j.val) = e 2 * (e 3 * (e 6 * (e 7 * (e 9)))) := by
  have h : (fun j : Fin 11 => (716 : ℕ).testBit j.val) = ![false, false, true, true, false, false, true, true, false, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask716 : matrixProduct (fun j => (716 : ℕ).testBit j.val) =
    decodeRows r657Rows := by
  rw [matrixProduct, expand_mask716]
  change decodeRows e2Rows * (decodeRows e3Rows * (decodeRows e6Rows * (decodeRows e7Rows * (decodeRows e9Rows)))) = _
  rw [decoded_product product_857, decoded_product product_858, decoded_product product_859, decoded_product product_860]

lemma expand_mask868 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (868 : ℕ).testBit j.val) = e 2 * (e 5 * (e 6 * (e 8 * (e 9)))) := by
  have h : (fun j : Fin 11 => (868 : ℕ).testBit j.val) = ![false, false, true, false, false, true, true, false, true, true, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask868 : matrixProduct (fun j => (868 : ℕ).testBit j.val) =
    decodeRows r672Rows := by
  rw [matrixProduct, expand_mask868]
  change decodeRows e2Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e9Rows)))) = _
  rw [decoded_product product_742, decoded_product product_807, decoded_product product_808, decoded_product product_861]

lemma expand_mask390 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (390 : ℕ).testBit j.val) = e 1 * (e 2 * (e 7 * (e 8))) := by
  have h : (fun j : Fin 11 => (390 : ℕ).testBit j.val) = ![false, true, true, false, false, false, false, true, true, false, false] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask390 : matrixProduct (fun j => (390 : ℕ).testBit j.val) =
    decodeRows r693Rows := by
  rw [matrixProduct, expand_mask390]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e7Rows * (decodeRows e8Rows))) = _
  rw [decoded_product product_774, decoded_product product_862, decoded_product product_863]

lemma expand_mask1642 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1642 : ℕ).testBit j.val) = e 1 * (e 3 * (e 5 * (e 6 * (e 9 * (e 10))))) := by
  have h : (fun j : Fin 11 => (1642 : ℕ).testBit j.val) = ![false, true, false, true, false, true, true, false, false, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1642 : matrixProduct (fun j => (1642 : ℕ).testBit j.val) =
    decodeRows r713Rows := by
  rw [matrixProduct, expand_mask1642]
  change decodeRows e1Rows * (decodeRows e3Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e9Rows * (decodeRows e10Rows))))) = _
  rw [decoded_product product_779, decoded_product product_795, decoded_product product_813, decoded_product product_814, decoded_product product_864]

lemma expand_mask1894 {M : Type*} [Monoid M] (e : Fin 11 → M) :
    binaryProduct e (fun j => (1894 : ℕ).testBit j.val) = e 1 * (e 2 * (e 5 * (e 6 * (e 8 * (e 9 * (e 10)))))) := by
  have h : (fun j : Fin 11 => (1894 : ℕ).testBit j.val) = ![false, true, true, false, false, true, true, false, true, true, true] := by
    funext j
    fin_cases j <;> decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ]

lemma eval_mask1894 : matrixProduct (fun j => (1894 : ℕ).testBit j.val) =
    decodeRows r734Rows := by
  rw [matrixProduct, expand_mask1894]
  change decodeRows e1Rows * (decodeRows e2Rows * (decodeRows e5Rows * (decodeRows e6Rows * (decodeRows e8Rows * (decodeRows e9Rows * (decodeRows e10Rows)))))) = _
  rw [decoded_product product_779, decoded_product product_780, decoded_product product_865, decoded_product product_866, decoded_product product_867, decoded_product product_868]


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
