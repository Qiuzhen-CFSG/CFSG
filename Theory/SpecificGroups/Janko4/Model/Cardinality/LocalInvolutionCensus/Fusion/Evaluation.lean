module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Bridge
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.ProductsCommon
import Mathlib.Tactic.FinCases

/-!
# Evaluating the actual source census words

The evaluations use the certified max2 kernel factors and the exact source
lifts. The target evaluations use the max1 seed itself. Thus no comparison
of matrix ranks, class table, or ambient general-linear conjugacy is involved.
See `source/README.md` for the ATLAS word and representation attribution.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates
open Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations (decoded_product eval_mul eval_inv)

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Common

private theorem decode_lift2 : decodeRows lift2Rows = decodeRows xyRows ^ 7 := by
  have h2 : decodeRows xyRowsP2 = decodeRows xyRows ^ 2 := by
    rw [← decoded_product product_00, ← pow_two]
  have h3 : decodeRows xyRowsP3 = decodeRows xyRows ^ 3 := by
    rw [← decoded_product product_01, h2, ← pow_succ]
  have h6 : decodeRows xyRowsP6 = decodeRows xyRows ^ 6 := by
    rw [← decoded_product product_02, h3, ← pow_add]
  have h := decoded_product product_03
  rw [h6, ← pow_succ] at h
  exact h.symm

private theorem decode_xy5 : decodeRows xy5Rows = decodeRows xyRows ^ 5 := by
  have h2 : decodeRows xyRowsP2 = decodeRows xyRows ^ 2 := by
    rw [← decoded_product product_04, ← pow_two]
  have h4 : decodeRows xyRowsP4 = decodeRows xyRows ^ 4 := by
    rw [← decoded_product product_05, h2, ← pow_add]
  have h := decoded_product product_06
  rw [h4, ← pow_succ] at h
  exact h.symm

private theorem decode_lift3 : decodeRows lift3Rows = decodeRows lift3BaseRows ^ 4 := by
  have h2 : decodeRows lift3BaseRowsP2 = decodeRows lift3BaseRows ^ 2 := by
    rw [← decoded_product product_08, ← pow_two]
  have h := decoded_product product_09
  rw [h2, ← pow_add] at h
  exact h.symm

theorem eval_lift (i : Fin 4) :
    toMatrix (sourceLift i : Model) =
      decodeRows (![packedOne, w10Rows, lift2Rows, lift3Rows] i) := by
  fin_cases i
  · exact (map_one toMatrix).trans decode_packedOne.symm
  · exact eval_w10
  · change toMatrix (xy ^ 7) = decodeRows lift2Rows
    rw [map_pow, eval_xy, decode_lift2]
  · change toMatrix ((xy ^ 5 * w14) ^ 4) = decodeRows lift3Rows
    rw [map_pow, map_mul, map_pow, eval_xy, eval_w14, ← decode_xy5,
      decoded_product product_07, decode_lift3]

private theorem expand_mask_0 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (0 : ℕ).testBit j.val then e j else 1)).prod =
      1 := by
  have hv : (fun j : Fin 13 => if (0 : ℕ).testBit j.val then e j else 1) =
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_0 : toMatrix (kernelProduct 0 : Model) = decodeRows packedOne := by
  have hk := expand_mask_0 kernelFactor
  change kernelProduct 0 = _ at hk
  rw [hk]
  exact (map_one toMatrix).trans decode_packedOne.symm

private theorem expand_mask_1 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (1 : ℕ).testBit j.val then e j else 1)).prod =
      e 0 := by
  have hv : (fun j : Fin 13 => if (1 : ℕ).testBit j.val then e j else 1) =
      ![e 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_1 : toMatrix (kernelProduct 1 : Model) = decodeRows (factorRows 0) := by
  have hk := expand_mask_1 kernelFactor
  change kernelProduct 1 = _ at hk
  rw [hk]
  exact eval_factor 0

private theorem expand_mask_6 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (6 : ℕ).testBit j.val then e j else 1)).prod =
      e 1 * (e 2) := by
  have hv : (fun j : Fin 13 => if (6 : ℕ).testBit j.val then e j else 1) =
      ![1, e 1, e 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_6 : toMatrix (kernelProduct 6 : Model) = decodeRows kernel6At1Rows := by
  have hk := expand_mask_6 kernelFactor
  change kernelProduct 6 = _ at hk
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_20]

private theorem expand_mask_26 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (26 : ℕ).testBit j.val then e j else 1)).prod =
      e 1 * (e 3 * (e 4)) := by
  have hv : (fun j : Fin 13 => if (26 : ℕ).testBit j.val then e j else 1) =
      ![1, e 1, 1, e 3, e 4, 1, 1, 1, 1, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_26 : toMatrix (kernelProduct 26 : Model) = decodeRows kernel26At1Rows := by
  have hk := expand_mask_26 kernelFactor
  change kernelProduct 26 = _ at hk
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_21, decoded_product product_22]

private theorem expand_mask_12 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (12 : ℕ).testBit j.val then e j else 1)).prod =
      e 2 * (e 3) := by
  have hv : (fun j : Fin 13 => if (12 : ℕ).testBit j.val then e j else 1) =
      ![1, 1, e 2, e 3, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_12 : toMatrix (kernelProduct 12 : Model) = decodeRows kernel12At2Rows := by
  have hk := expand_mask_12 kernelFactor
  change kernelProduct 12 = _ at hk
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_23]

private theorem expand_mask_304 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (304 : ℕ).testBit j.val then e j else 1)).prod =
      e 4 * (e 5 * (e 8)) := by
  have hv : (fun j : Fin 13 => if (304 : ℕ).testBit j.val then e j else 1) =
      ![1, 1, 1, 1, e 4, e 5, 1, 1, e 8, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_304 : toMatrix (kernelProduct 304 : Model) = decodeRows kernel304At4Rows := by
  have hk := expand_mask_304 kernelFactor
  change kernelProduct 304 = _ at hk
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_24, decoded_product product_25]

private theorem expand_mask_305 {M : Type*} [Monoid M] (e : Fin 13 → M) :
    (List.ofFn (fun j : Fin 13 => if (305 : ℕ).testBit j.val then e j else 1)).prod =
      e 0 * (e 4 * (e 5 * (e 8))) := by
  have hv : (fun j : Fin 13 => if (305 : ℕ).testBit j.val then e j else 1) =
      ![e 0, 1, 1, 1, e 4, e 5, 1, 1, e 8, 1, 1, 1, 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  simp [List.ofFn_succ]

theorem eval_kernel_305 : toMatrix (kernelProduct 305 : Model) = decodeRows kernel305At0Rows := by
  have hk := expand_mask_305 kernelFactor
  change kernelProduct 305 = _ at hk
  rw [hk]
  simp only [Subgroup.coe_mul, map_mul, eval_factor]
  rw [decoded_product product_26, decoded_product product_27, decoded_product product_28]

private theorem eval_source_seed_sq :
    toMatrix ((sourceSeed ^ 2 : sourceSubgroup) : Model) = decodeRows (factorRows 0) :=
  eval_factor 0

private theorem eval_a : toMatrix Janko4.a = decodeRows aRows := rfl
private theorem eval_b : toMatrix Janko4.b = decodeRows bRows := rfl

private theorem eval_a_inv : toMatrix Janko4.a⁻¹ = decodeRows aRows :=
  eval_inv toMatrix eval_a matrixA_mul_self

attribute [local irreducible] modelGroup matrixA matrixB sourceSubgroup kernelProduct kernelFactor sourceLift

theorem eval_rep_0 : toMatrix (sourceRepresentative 0 : Model) = decodeRows packedOne := by
  change toMatrix ((kernelProduct 0 : Model) * (sourceLift 0 : Model)) = _
  rw [map_mul, eval_kernel_0, eval_lift]
  rw [show (![packedOne, w10Rows, lift2Rows, lift3Rows] (0 : Fin 4)) = packedOne from rfl, decode_packedOne, mul_one]

theorem eval_translated_0 : toMatrix (sourceTranslated 0 : Model) = decodeRows (factorRows 0) := by
  change toMatrix ((sourceRepresentative 0 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_0]
  rw [eval_source_seed_sq]
  rw [decode_packedOne, one_mul]

theorem eval_rep_1 : toMatrix (sourceRepresentative 1 : Model) = decodeRows (factorRows 0) := by
  change toMatrix ((kernelProduct 1 : Model) * (sourceLift 0 : Model)) = _
  rw [map_mul, eval_kernel_1, eval_lift]
  rw [show (![packedOne, w10Rows, lift2Rows, lift3Rows] (0 : Fin 4)) = packedOne from rfl, decode_packedOne, mul_one]

theorem eval_translated_1 : toMatrix (sourceTranslated 1 : Model) = decodeRows packedOne := by
  change toMatrix ((sourceRepresentative 1 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_1]
  rw [eval_source_seed_sq]
  exact decoded_product product_29

theorem eval_rep_2 : toMatrix (sourceRepresentative 2 : Model) = decodeRows kernel6At1Rows := by
  change toMatrix ((kernelProduct 6 : Model) * (sourceLift 0 : Model)) = _
  rw [map_mul, eval_kernel_6, eval_lift]
  rw [show (![packedOne, w10Rows, lift2Rows, lift3Rows] (0 : Fin 4)) = packedOne from rfl, decode_packedOne, mul_one]

theorem eval_translated_2 : toMatrix (sourceTranslated 2 : Model) = decodeRows translate2Rows := by
  change toMatrix ((sourceRepresentative 2 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_2]
  rw [eval_source_seed_sq]
  exact decoded_product product_30

theorem eval_rep_3 : toMatrix (sourceRepresentative 3 : Model) = decodeRows kernel26At1Rows := by
  change toMatrix ((kernelProduct 26 : Model) * (sourceLift 0 : Model)) = _
  rw [map_mul, eval_kernel_26, eval_lift]
  rw [show (![packedOne, w10Rows, lift2Rows, lift3Rows] (0 : Fin 4)) = packedOne from rfl, decode_packedOne, mul_one]

theorem eval_translated_3 : toMatrix (sourceTranslated 3 : Model) = decodeRows translate3Rows := by
  change toMatrix ((sourceRepresentative 3 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_3]
  rw [eval_source_seed_sq]
  exact decoded_product product_31

theorem eval_rep_4 : toMatrix (sourceRepresentative 4 : Model) = decodeRows w10Rows := by
  change toMatrix ((kernelProduct 0 : Model) * (sourceLift 1 : Model)) = _
  rw [map_mul, eval_kernel_0, eval_lift]
  rw [decode_packedOne, one_mul]
  rfl

theorem eval_translated_4 : toMatrix (sourceTranslated 4 : Model) = decodeRows translate4Rows := by
  change toMatrix ((sourceRepresentative 4 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_4]
  rw [eval_source_seed_sq]
  exact decoded_product product_32

theorem eval_rep_5 : toMatrix (sourceRepresentative 5 : Model) = decodeRows lift2Rows := by
  change toMatrix ((kernelProduct 0 : Model) * (sourceLift 2 : Model)) = _
  rw [map_mul, eval_kernel_0, eval_lift]
  rw [decode_packedOne, one_mul]
  rfl

theorem eval_translated_5 : toMatrix (sourceTranslated 5 : Model) = decodeRows translate5Rows := by
  change toMatrix ((sourceRepresentative 5 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_5]
  rw [eval_source_seed_sq]
  exact decoded_product product_33

theorem eval_rep_6 : toMatrix (sourceRepresentative 6 : Model) = decodeRows rep6Rows := by
  change toMatrix ((kernelProduct 1 : Model) * (sourceLift 2 : Model)) = _
  rw [map_mul, eval_kernel_1, eval_lift]
  exact decoded_product product_34

theorem eval_translated_6 : toMatrix (sourceTranslated 6 : Model) = decodeRows translate6Rows := by
  change toMatrix ((sourceRepresentative 6 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_6]
  rw [eval_source_seed_sq]
  exact decoded_product product_35

theorem eval_rep_7 : toMatrix (sourceRepresentative 7 : Model) = decodeRows lift3Rows := by
  change toMatrix ((kernelProduct 0 : Model) * (sourceLift 3 : Model)) = _
  rw [map_mul, eval_kernel_0, eval_lift]
  rw [decode_packedOne, one_mul]
  rfl

theorem eval_translated_7 : toMatrix (sourceTranslated 7 : Model) = decodeRows translate7Rows := by
  change toMatrix ((sourceRepresentative 7 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_7]
  rw [eval_source_seed_sq]
  exact decoded_product product_36

theorem eval_rep_8 : toMatrix (sourceRepresentative 8 : Model) = decodeRows rep8Rows := by
  change toMatrix ((kernelProduct 12 : Model) * (sourceLift 3 : Model)) = _
  rw [map_mul, eval_kernel_12, eval_lift]
  exact decoded_product product_37

theorem eval_translated_8 : toMatrix (sourceTranslated 8 : Model) = decodeRows translate8Rows := by
  change toMatrix ((sourceRepresentative 8 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_8]
  rw [eval_source_seed_sq]
  exact decoded_product product_38

theorem eval_rep_9 : toMatrix (sourceRepresentative 9 : Model) = decodeRows rep9Rows := by
  change toMatrix ((kernelProduct 304 : Model) * (sourceLift 3 : Model)) = _
  rw [map_mul, eval_kernel_304, eval_lift]
  exact decoded_product product_39

theorem eval_translated_9 : toMatrix (sourceTranslated 9 : Model) = decodeRows translate9Rows := by
  change toMatrix ((sourceRepresentative 9 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_9]
  rw [eval_source_seed_sq]
  exact decoded_product product_40

theorem eval_rep_10 : toMatrix (sourceRepresentative 10 : Model) = decodeRows rep10Rows := by
  change toMatrix ((kernelProduct 305 : Model) * (sourceLift 3 : Model)) = _
  rw [map_mul, eval_kernel_305, eval_lift]
  exact decoded_product product_41

theorem eval_translated_10 : toMatrix (sourceTranslated 10 : Model) = decodeRows translate10Rows := by
  change toMatrix ((sourceRepresentative 10 : Model) * ((sourceSeed ^ 2 : sourceSubgroup) : Model)) = _
  rw [map_mul, eval_rep_10]
  rw [eval_source_seed_sq]
  exact decoded_product product_42

private theorem eval_b2 : toMatrix (Janko4.b ^ 2) = decodeRows bSquareRows := by
  rw [map_pow, pow_two, eval_b, decoded_product product_10]

private theorem eval_b3 : toMatrix (Janko4.b ^ 3) = decodeRows bCubeRows := by
  rw [pow_succ, map_mul, eval_b2, eval_b, decoded_product product_11]

private theorem eval_b2_inv : toMatrix (Janko4.b ^ 2)⁻¹ = decodeRows bSquareRows :=
  eval_inv toMatrix eval_b2 (by rw [decoded_product product_12, decode_packedOne])

private theorem eval_b3_inv : toMatrix (Janko4.b ^ 3)⁻¹ = decodeRows bRows :=
  eval_inv toMatrix eval_b3 (by rw [decoded_product product_13, decode_packedOne])

theorem eval_aztRows : toMatrix (Janko4.a * t * Janko4.a⁻¹) = decodeRows aztRows :=
  eval_mul toMatrix (eval_mul toMatrix eval_a eval_target (decoded_product product_14))
    eval_a_inv (decoded_product product_15)

theorem eval_bbzaRows : toMatrix (Janko4.b ^ 2 * Janko4.a * (Janko4.b ^ 2)⁻¹) = decodeRows bbzaRows :=
  eval_mul toMatrix (eval_mul toMatrix eval_b2 eval_a (decoded_product product_16))
    eval_b2_inv (decoded_product product_17)

theorem eval_bbbzaRows : toMatrix (Janko4.b ^ 3 * Janko4.a * (Janko4.b ^ 3)⁻¹) = decodeRows bbbzaRows :=
  eval_mul toMatrix (eval_mul toMatrix eval_b3 eval_a (decoded_product product_18))
    eval_b3_inv (decoded_product product_19)

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
