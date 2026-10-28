module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Algebraic
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-6 transition batches 3–16

These fourteen batches comprise 560 permutation identities: 460 proved by
word normalization and 100 by exhaustive checks on all 4060 points.
The fixed ATLAS word witnesses and multiplication convention are documented
in `OrderLevel0Data`. Finite case analysis below covers both forward generators
and all twenty representatives of each batch; `ofStepBatchCheck` converts the
verified checks to the original permutation identities.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0
set_option Elab.async false

/-- Resolve the row coordinates before matching the transition predicate. -/
private theorem ofRow {i : Fin 2} {r : Fin 4060} (k : Fin 100)
    (hr : FactorWords.row k = (i, r))
    (h : stepCheck (FactorWords.row k).1 (FactorWords.row k).2) : stepCheck i r := by
  rw [hr] at h
  exact h

private theorem checked3 : stepBatch 27 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point3_0_0
  · exact Algebraic.point3_0_1
  · exact Algebraic.point3_0_2
  · exact Algebraic.point3_0_3
  · exact ofRow ⟨0, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨0, by decide⟩)
  · exact Algebraic.point3_0_5
  · exact Algebraic.point3_0_6
  · exact Algebraic.point3_0_7
  · exact Algebraic.point3_0_8
  · exact Algebraic.point3_0_9
  · exact Algebraic.point3_0_10
  · exact Algebraic.point3_0_11
  · exact ofRow ⟨1, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨1, by decide⟩)
  · exact Algebraic.point3_0_13
  · exact ofRow ⟨2, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨2, by decide⟩)
  · exact Algebraic.point3_0_15
  · exact Algebraic.point3_0_16
  · exact Algebraic.point3_0_17
  · exact Algebraic.point3_0_18
  · exact Algebraic.point3_0_19
  · exact Algebraic.point3_1_0
  · exact Algebraic.point3_1_1
  · exact Algebraic.point3_1_2
  · exact Algebraic.point3_1_3
  · exact Algebraic.point3_1_4
  · exact ofRow ⟨3, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨3, by decide⟩)
  · exact Algebraic.point3_1_6
  · exact Algebraic.point3_1_7
  · exact Algebraic.point3_1_8
  · exact Algebraic.point3_1_9
  · exact Algebraic.point3_1_10
  · exact Algebraic.point3_1_11
  · exact Algebraic.point3_1_12
  · exact Algebraic.point3_1_13
  · exact Algebraic.point3_1_14
  · exact Algebraic.point3_1_15
  · exact ofRow ⟨4, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨4, by decide⟩)
  · exact Algebraic.point3_1_17
  · exact Algebraic.point3_1_18
  · exact Algebraic.point3_1_19

private theorem checked4 : stepBatch 34 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point4_0_0
  · exact Algebraic.point4_0_1
  · exact Algebraic.point4_0_2
  · exact Algebraic.point4_0_3
  · exact Algebraic.point4_0_4
  · exact Algebraic.point4_0_5
  · exact Algebraic.point4_0_6
  · exact Algebraic.point4_0_7
  · exact Algebraic.point4_0_8
  · exact Algebraic.point4_0_9
  · exact Algebraic.point4_0_10
  · exact Algebraic.point4_0_11
  · exact Algebraic.point4_0_12
  · exact Algebraic.point4_0_13
  · exact Algebraic.point4_0_14
  · exact Algebraic.point4_0_15
  · exact Algebraic.point4_0_16
  · exact Algebraic.point4_0_17
  · exact Algebraic.point4_0_18
  · exact Algebraic.point4_0_19
  · exact Algebraic.point4_1_0
  · exact Algebraic.point4_1_1
  · exact Algebraic.point4_1_2
  · exact ofRow ⟨5, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨5, by decide⟩)
  · exact Algebraic.point4_1_4
  · exact Algebraic.point4_1_5
  · exact Algebraic.point4_1_6
  · exact Algebraic.point4_1_7
  · exact Algebraic.point4_1_8
  · exact Algebraic.point4_1_9
  · exact Algebraic.point4_1_10
  · exact Algebraic.point4_1_11
  · exact Algebraic.point4_1_12
  · exact Algebraic.point4_1_13
  · exact Algebraic.point4_1_14
  · exact Algebraic.point4_1_15
  · exact ofRow ⟨6, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨6, by decide⟩)
  · exact Algebraic.point4_1_17
  · exact Algebraic.point4_1_18
  · exact ofRow ⟨7, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨7, by decide⟩)

private theorem checked5 : stepBatch 41 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point5_0_0
  · exact Algebraic.point5_0_1
  · exact Algebraic.point5_0_2
  · exact Algebraic.point5_0_3
  · exact Algebraic.point5_0_4
  · exact Algebraic.point5_0_5
  · exact Algebraic.point5_0_6
  · exact Algebraic.point5_0_7
  · exact Algebraic.point5_0_8
  · exact Algebraic.point5_0_9
  · exact ofRow ⟨8, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨8, by decide⟩)
  · exact Algebraic.point5_0_11
  · exact Algebraic.point5_0_12
  · exact Algebraic.point5_0_13
  · exact Algebraic.point5_0_14
  · exact Algebraic.point5_0_15
  · exact Algebraic.point5_0_16
  · exact Algebraic.point5_0_17
  · exact Algebraic.point5_0_18
  · exact Algebraic.point5_0_19
  · exact Algebraic.point5_1_0
  · exact Algebraic.point5_1_1
  · exact Algebraic.point5_1_2
  · exact Algebraic.point5_1_3
  · exact Algebraic.point5_1_4
  · exact Algebraic.point5_1_5
  · exact Algebraic.point5_1_6
  · exact Algebraic.point5_1_7
  · exact ofRow ⟨9, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨9, by decide⟩)
  · exact ofRow ⟨10, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨10, by decide⟩)
  · exact Algebraic.point5_1_10
  · exact Algebraic.point5_1_11
  · exact Algebraic.point5_1_12
  · exact Algebraic.point5_1_13
  · exact Algebraic.point5_1_14
  · exact Algebraic.point5_1_15
  · exact Algebraic.point5_1_16
  · exact Algebraic.point5_1_17
  · exact Algebraic.point5_1_18
  · exact Algebraic.point5_1_19

private theorem checked6 : stepBatch 48 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point6_0_0
  · exact Algebraic.point6_0_1
  · exact Algebraic.point6_0_2
  · exact Algebraic.point6_0_3
  · exact Algebraic.point6_0_4
  · exact Algebraic.point6_0_5
  · exact ofRow ⟨11, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨11, by decide⟩)
  · exact Algebraic.point6_0_7
  · exact Algebraic.point6_0_8
  · exact Algebraic.point6_0_9
  · exact Algebraic.point6_0_10
  · exact Algebraic.point6_0_11
  · exact Algebraic.point6_0_12
  · exact Algebraic.point6_0_13
  · exact Algebraic.point6_0_14
  · exact Algebraic.point6_0_15
  · exact ofRow ⟨12, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨12, by decide⟩)
  · exact Algebraic.point6_0_17
  · exact Algebraic.point6_0_18
  · exact Algebraic.point6_0_19
  · exact Algebraic.point6_1_0
  · exact Algebraic.point6_1_1
  · exact Algebraic.point6_1_2
  · exact Algebraic.point6_1_3
  · exact Algebraic.point6_1_4
  · exact ofRow ⟨13, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨13, by decide⟩)
  · exact Algebraic.point6_1_6
  · exact ofRow ⟨14, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨14, by decide⟩)
  · exact Algebraic.point6_1_8
  · exact Algebraic.point6_1_9
  · exact Algebraic.point6_1_10
  · exact Algebraic.point6_1_11
  · exact Algebraic.point6_1_12
  · exact Algebraic.point6_1_13
  · exact Algebraic.point6_1_14
  · exact ofRow ⟨15, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨15, by decide⟩)
  · exact Algebraic.point6_1_16
  · exact Algebraic.point6_1_17
  · exact Algebraic.point6_1_18
  · exact Algebraic.point6_1_19

private theorem checked7 : stepBatch 55 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point7_0_0
  · exact Algebraic.point7_0_1
  · exact Algebraic.point7_0_2
  · exact Algebraic.point7_0_3
  · exact Algebraic.point7_0_4
  · exact Algebraic.point7_0_5
  · exact Algebraic.point7_0_6
  · exact Algebraic.point7_0_7
  · exact Algebraic.point7_0_8
  · exact Algebraic.point7_0_9
  · exact Algebraic.point7_0_10
  · exact ofRow ⟨16, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨16, by decide⟩)
  · exact Algebraic.point7_0_12
  · exact Algebraic.point7_0_13
  · exact Algebraic.point7_0_14
  · exact Algebraic.point7_0_15
  · exact Algebraic.point7_0_16
  · exact Algebraic.point7_0_17
  · exact Algebraic.point7_0_18
  · exact Algebraic.point7_0_19
  · exact Algebraic.point7_1_0
  · exact Algebraic.point7_1_1
  · exact Algebraic.point7_1_2
  · exact Algebraic.point7_1_3
  · exact ofRow ⟨17, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨17, by decide⟩)
  · exact Algebraic.point7_1_5
  · exact Algebraic.point7_1_6
  · exact ofRow ⟨18, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨18, by decide⟩)
  · exact Algebraic.point7_1_8
  · exact Algebraic.point7_1_9
  · exact Algebraic.point7_1_10
  · exact Algebraic.point7_1_11
  · exact Algebraic.point7_1_12
  · exact Algebraic.point7_1_13
  · exact Algebraic.point7_1_14
  · exact Algebraic.point7_1_15
  · exact Algebraic.point7_1_16
  · exact Algebraic.point7_1_17
  · exact Algebraic.point7_1_18
  · exact ofRow ⟨19, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨19, by decide⟩)

private theorem checked8 : stepBatch 62 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point8_0_0
  · exact Algebraic.point8_0_1
  · exact Algebraic.point8_0_2
  · exact Algebraic.point8_0_3
  · exact Algebraic.point8_0_4
  · exact Algebraic.point8_0_5
  · exact Algebraic.point8_0_6
  · exact Algebraic.point8_0_7
  · exact ofRow ⟨20, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨20, by decide⟩)
  · exact Algebraic.point8_0_9
  · exact Algebraic.point8_0_10
  · exact Algebraic.point8_0_11
  · exact Algebraic.point8_0_12
  · exact ofRow ⟨21, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨21, by decide⟩)
  · exact Algebraic.point8_0_14
  · exact Algebraic.point8_0_15
  · exact Algebraic.point8_0_16
  · exact Algebraic.point8_0_17
  · exact Algebraic.point8_0_18
  · exact Algebraic.point8_0_19
  · exact Algebraic.point8_1_0
  · exact ofRow ⟨22, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨22, by decide⟩)
  · exact Algebraic.point8_1_2
  · exact Algebraic.point8_1_3
  · exact Algebraic.point8_1_4
  · exact Algebraic.point8_1_5
  · exact Algebraic.point8_1_6
  · exact Algebraic.point8_1_7
  · exact Algebraic.point8_1_8
  · exact ofRow ⟨23, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨23, by decide⟩)
  · exact Algebraic.point8_1_10
  · exact Algebraic.point8_1_11
  · exact Algebraic.point8_1_12
  · exact ofRow ⟨24, by decide⟩ (by decide +kernel)
      (Dense0.checked ⟨24, by decide⟩)
  · exact ofRow ⟨25, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨0, by decide⟩)
  · exact Algebraic.point8_1_15
  · exact Algebraic.point8_1_16
  · exact Algebraic.point8_1_17
  · exact Algebraic.point8_1_18
  · exact Algebraic.point8_1_19

private theorem checked9 : stepBatch 69 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point9_0_0
  · exact Algebraic.point9_0_1
  · exact Algebraic.point9_0_2
  · exact Algebraic.point9_0_3
  · exact Algebraic.point9_0_4
  · exact ofRow ⟨26, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨1, by decide⟩)
  · exact Algebraic.point9_0_6
  · exact ofRow ⟨27, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨2, by decide⟩)
  · exact ofRow ⟨28, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨3, by decide⟩)
  · exact Algebraic.point9_0_9
  · exact Algebraic.point9_0_10
  · exact Algebraic.point9_0_11
  · exact ofRow ⟨29, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨4, by decide⟩)
  · exact Algebraic.point9_0_13
  · exact Algebraic.point9_0_14
  · exact Algebraic.point9_0_15
  · exact ofRow ⟨30, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨5, by decide⟩)
  · exact ofRow ⟨31, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨6, by decide⟩)
  · exact Algebraic.point9_0_18
  · exact ofRow ⟨32, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨7, by decide⟩)
  · exact Algebraic.point9_1_0
  · exact Algebraic.point9_1_1
  · exact Algebraic.point9_1_2
  · exact Algebraic.point9_1_3
  · exact Algebraic.point9_1_4
  · exact Algebraic.point9_1_5
  · exact Algebraic.point9_1_6
  · exact Algebraic.point9_1_7
  · exact Algebraic.point9_1_8
  · exact Algebraic.point9_1_9
  · exact ofRow ⟨33, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨8, by decide⟩)
  · exact Algebraic.point9_1_11
  · exact Algebraic.point9_1_12
  · exact Algebraic.point9_1_13
  · exact Algebraic.point9_1_14
  · exact Algebraic.point9_1_15
  · exact Algebraic.point9_1_16
  · exact Algebraic.point9_1_17
  · exact Algebraic.point9_1_18
  · exact ofRow ⟨34, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨9, by decide⟩)

private theorem checked10 : stepBatch 76 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point10_0_0
  · exact Algebraic.point10_0_1
  · exact Algebraic.point10_0_2
  · exact Algebraic.point10_0_3
  · exact Algebraic.point10_0_4
  · exact Algebraic.point10_0_5
  · exact Algebraic.point10_0_6
  · exact Algebraic.point10_0_7
  · exact ofRow ⟨35, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨10, by decide⟩)
  · exact Algebraic.point10_0_9
  · exact Algebraic.point10_0_10
  · exact ofRow ⟨36, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨11, by decide⟩)
  · exact Algebraic.point10_0_12
  · exact Algebraic.point10_0_13
  · exact Algebraic.point10_0_14
  · exact Algebraic.point10_0_15
  · exact Algebraic.point10_0_16
  · exact Algebraic.point10_0_17
  · exact Algebraic.point10_0_18
  · exact Algebraic.point10_0_19
  · exact Algebraic.point10_1_0
  · exact Algebraic.point10_1_1
  · exact Algebraic.point10_1_2
  · exact Algebraic.point10_1_3
  · exact Algebraic.point10_1_4
  · exact ofRow ⟨37, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨12, by decide⟩)
  · exact Algebraic.point10_1_6
  · exact Algebraic.point10_1_7
  · exact Algebraic.point10_1_8
  · exact ofRow ⟨38, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨13, by decide⟩)
  · exact Algebraic.point10_1_10
  · exact Algebraic.point10_1_11
  · exact ofRow ⟨39, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨14, by decide⟩)
  · exact Algebraic.point10_1_13
  · exact Algebraic.point10_1_14
  · exact ofRow ⟨40, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨15, by decide⟩)
  · exact Algebraic.point10_1_16
  · exact Algebraic.point10_1_17
  · exact Algebraic.point10_1_18
  · exact Algebraic.point10_1_19

private theorem checked11 : stepBatch 83 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point11_0_0
  · exact Algebraic.point11_0_1
  · exact Algebraic.point11_0_2
  · exact Algebraic.point11_0_3
  · exact ofRow ⟨41, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨16, by decide⟩)
  · exact Algebraic.point11_0_5
  · exact Algebraic.point11_0_6
  · exact ofRow ⟨42, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨17, by decide⟩)
  · exact Algebraic.point11_0_8
  · exact Algebraic.point11_0_9
  · exact Algebraic.point11_0_10
  · exact Algebraic.point11_0_11
  · exact Algebraic.point11_0_12
  · exact Algebraic.point11_0_13
  · exact Algebraic.point11_0_14
  · exact Algebraic.point11_0_15
  · exact Algebraic.point11_0_16
  · exact Algebraic.point11_0_17
  · exact Algebraic.point11_0_18
  · exact ofRow ⟨43, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨18, by decide⟩)
  · exact Algebraic.point11_1_0
  · exact Algebraic.point11_1_1
  · exact Algebraic.point11_1_2
  · exact ofRow ⟨44, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨19, by decide⟩)
  · exact Algebraic.point11_1_4
  · exact Algebraic.point11_1_5
  · exact Algebraic.point11_1_6
  · exact Algebraic.point11_1_7
  · exact Algebraic.point11_1_8
  · exact Algebraic.point11_1_9
  · exact Algebraic.point11_1_10
  · exact ofRow ⟨45, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨20, by decide⟩)
  · exact ofRow ⟨46, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨21, by decide⟩)
  · exact ofRow ⟨47, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨22, by decide⟩)
  · exact Algebraic.point11_1_14
  · exact Algebraic.point11_1_15
  · exact Algebraic.point11_1_16
  · exact ofRow ⟨48, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨23, by decide⟩)
  · exact Algebraic.point11_1_18
  · exact Algebraic.point11_1_19

private theorem checked12 : stepBatch 90 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact ofRow ⟨49, by decide⟩ (by decide +kernel)
      (Dense1.checked ⟨24, by decide⟩)
  · exact Algebraic.point12_0_1
  · exact Algebraic.point12_0_2
  · exact ofRow ⟨50, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨0, by decide⟩)
  · exact Algebraic.point12_0_4
  · exact Algebraic.point12_0_5
  · exact Algebraic.point12_0_6
  · exact ofRow ⟨51, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨1, by decide⟩)
  · exact Algebraic.point12_0_8
  · exact Algebraic.point12_0_9
  · exact Algebraic.point12_0_10
  · exact Algebraic.point12_0_11
  · exact Algebraic.point12_0_12
  · exact ofRow ⟨52, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨2, by decide⟩)
  · exact ofRow ⟨53, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨3, by decide⟩)
  · exact Algebraic.point12_0_15
  · exact Algebraic.point12_0_16
  · exact ofRow ⟨54, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨4, by decide⟩)
  · exact Algebraic.point12_0_18
  · exact Algebraic.point12_0_19
  · exact Algebraic.point12_1_0
  · exact Algebraic.point12_1_1
  · exact Algebraic.point12_1_2
  · exact Algebraic.point12_1_3
  · exact Algebraic.point12_1_4
  · exact ofRow ⟨55, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨5, by decide⟩)
  · exact Algebraic.point12_1_6
  · exact ofRow ⟨56, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨6, by decide⟩)
  · exact Algebraic.point12_1_8
  · exact Algebraic.point12_1_9
  · exact Algebraic.point12_1_10
  · exact ofRow ⟨57, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨7, by decide⟩)
  · exact Algebraic.point12_1_12
  · exact Algebraic.point12_1_13
  · exact Algebraic.point12_1_14
  · exact Algebraic.point12_1_15
  · exact Algebraic.point12_1_16
  · exact Algebraic.point12_1_17
  · exact Algebraic.point12_1_18
  · exact Algebraic.point12_1_19

private theorem checked13 : stepBatch 97 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact ofRow ⟨58, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨8, by decide⟩)
  · exact Algebraic.point13_0_1
  · exact ofRow ⟨59, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨9, by decide⟩)
  · exact ofRow ⟨60, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨10, by decide⟩)
  · exact ofRow ⟨61, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨11, by decide⟩)
  · exact ofRow ⟨62, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨12, by decide⟩)
  · exact Algebraic.point13_0_6
  · exact Algebraic.point13_0_7
  · exact Algebraic.point13_0_8
  · exact Algebraic.point13_0_9
  · exact Algebraic.point13_0_10
  · exact ofRow ⟨63, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨13, by decide⟩)
  · exact Algebraic.point13_0_12
  · exact Algebraic.point13_0_13
  · exact Algebraic.point13_0_14
  · exact Algebraic.point13_0_15
  · exact Algebraic.point13_0_16
  · exact ofRow ⟨64, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨14, by decide⟩)
  · exact Algebraic.point13_0_18
  · exact Algebraic.point13_0_19
  · exact Algebraic.point13_1_0
  · exact Algebraic.point13_1_1
  · exact Algebraic.point13_1_2
  · exact Algebraic.point13_1_3
  · exact Algebraic.point13_1_4
  · exact Algebraic.point13_1_5
  · exact ofRow ⟨65, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨15, by decide⟩)
  · exact Algebraic.point13_1_7
  · exact Algebraic.point13_1_8
  · exact Algebraic.point13_1_9
  · exact ofRow ⟨66, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨16, by decide⟩)
  · exact ofRow ⟨67, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨17, by decide⟩)
  · exact Algebraic.point13_1_12
  · exact Algebraic.point13_1_13
  · exact Algebraic.point13_1_14
  · exact Algebraic.point13_1_15
  · exact Algebraic.point13_1_16
  · exact Algebraic.point13_1_17
  · exact Algebraic.point13_1_18
  · exact Algebraic.point13_1_19

private theorem checked14 : stepBatch 104 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point14_0_0
  · exact Algebraic.point14_0_1
  · exact Algebraic.point14_0_2
  · exact ofRow ⟨68, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨18, by decide⟩)
  · exact Algebraic.point14_0_4
  · exact Algebraic.point14_0_5
  · exact Algebraic.point14_0_6
  · exact Algebraic.point14_0_7
  · exact ofRow ⟨69, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨19, by decide⟩)
  · exact Algebraic.point14_0_9
  · exact Algebraic.point14_0_10
  · exact Algebraic.point14_0_11
  · exact ofRow ⟨70, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨20, by decide⟩)
  · exact Algebraic.point14_0_13
  · exact ofRow ⟨71, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨21, by decide⟩)
  · exact Algebraic.point14_0_15
  · exact Algebraic.point14_0_16
  · exact ofRow ⟨72, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨22, by decide⟩)
  · exact Algebraic.point14_0_18
  · exact ofRow ⟨73, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨23, by decide⟩)
  · exact ofRow ⟨74, by decide⟩ (by decide +kernel)
      (Dense2.checked ⟨24, by decide⟩)
  · exact Algebraic.point14_1_1
  · exact ofRow ⟨75, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨0, by decide⟩)
  · exact Algebraic.point14_1_3
  · exact Algebraic.point14_1_4
  · exact Algebraic.point14_1_5
  · exact Algebraic.point14_1_6
  · exact Algebraic.point14_1_7
  · exact ofRow ⟨76, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨1, by decide⟩)
  · exact Algebraic.point14_1_9
  · exact ofRow ⟨77, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨2, by decide⟩)
  · exact Algebraic.point14_1_11
  · exact Algebraic.point14_1_12
  · exact Algebraic.point14_1_13
  · exact Algebraic.point14_1_14
  · exact Algebraic.point14_1_15
  · exact ofRow ⟨78, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨3, by decide⟩)
  · exact Algebraic.point14_1_17
  · exact ofRow ⟨79, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨4, by decide⟩)
  · exact ofRow ⟨80, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨5, by decide⟩)

private theorem checked15 : stepBatch 111 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact ofRow ⟨81, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨6, by decide⟩)
  · exact Algebraic.point15_0_1
  · exact ofRow ⟨82, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨7, by decide⟩)
  · exact Algebraic.point15_0_3
  · exact ofRow ⟨83, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨8, by decide⟩)
  · exact Algebraic.point15_0_5
  · exact Algebraic.point15_0_6
  · exact Algebraic.point15_0_7
  · exact Algebraic.point15_0_8
  · exact ofRow ⟨84, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨9, by decide⟩)
  · exact Algebraic.point15_0_10
  · exact Algebraic.point15_0_11
  · exact Algebraic.point15_0_12
  · exact Algebraic.point15_0_13
  · exact ofRow ⟨85, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨10, by decide⟩)
  · exact Algebraic.point15_0_15
  · exact Algebraic.point15_0_16
  · exact ofRow ⟨86, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨11, by decide⟩)
  · exact Algebraic.point15_0_18
  · exact ofRow ⟨87, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨12, by decide⟩)
  · exact Algebraic.point15_1_0
  · exact Algebraic.point15_1_1
  · exact Algebraic.point15_1_2
  · exact Algebraic.point15_1_3
  · exact ofRow ⟨88, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨13, by decide⟩)
  · exact Algebraic.point15_1_5
  · exact Algebraic.point15_1_6
  · exact Algebraic.point15_1_7
  · exact Algebraic.point15_1_8
  · exact Algebraic.point15_1_9
  · exact ofRow ⟨89, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨14, by decide⟩)
  · exact Algebraic.point15_1_11
  · exact Algebraic.point15_1_12
  · exact Algebraic.point15_1_13
  · exact Algebraic.point15_1_14
  · exact Algebraic.point15_1_15
  · exact Algebraic.point15_1_16
  · exact Algebraic.point15_1_17
  · exact Algebraic.point15_1_18
  · exact Algebraic.point15_1_19

private theorem checked16 : stepBatch 118 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact Algebraic.point16_0_0
  · exact Algebraic.point16_0_1
  · exact Algebraic.point16_0_2
  · exact ofRow ⟨90, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨15, by decide⟩)
  · exact ofRow ⟨91, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨16, by decide⟩)
  · exact ofRow ⟨92, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨17, by decide⟩)
  · exact Algebraic.point16_0_6
  · exact Algebraic.point16_0_7
  · exact Algebraic.point16_0_8
  · exact ofRow ⟨93, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨18, by decide⟩)
  · exact Algebraic.point16_0_10
  · exact Algebraic.point16_0_11
  · exact Algebraic.point16_0_12
  · exact Algebraic.point16_0_13
  · exact ofRow ⟨94, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨19, by decide⟩)
  · exact Algebraic.point16_0_15
  · exact Algebraic.point16_0_16
  · exact Algebraic.point16_0_17
  · exact ofRow ⟨95, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨20, by decide⟩)
  · exact Algebraic.point16_0_19
  · exact Algebraic.point16_1_0
  · exact Algebraic.point16_1_1
  · exact Algebraic.point16_1_2
  · exact Algebraic.point16_1_3
  · exact Algebraic.point16_1_4
  · exact Algebraic.point16_1_5
  · exact Algebraic.point16_1_6
  · exact ofRow ⟨96, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨21, by decide⟩)
  · exact Algebraic.point16_1_8
  · exact Algebraic.point16_1_9
  · exact Algebraic.point16_1_10
  · exact Algebraic.point16_1_11
  · exact Algebraic.point16_1_12
  · exact ofRow ⟨97, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨22, by decide⟩)
  · exact Algebraic.point16_1_14
  · exact Algebraic.point16_1_15
  · exact ofRow ⟨98, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨23, by decide⟩)
  · exact Algebraic.point16_1_17
  · exact ofRow ⟨99, by decide⟩ (by decide +kernel)
      (Dense3.checked ⟨24, by decide⟩)
  · exact Algebraic.point16_1_19

/-- All forward transitions in local part-6 batches 3 through 16. -/
public theorem checked (b : Fin 14) :
    stepBatch ⟨7 * (b.val + 3) + 6, by omega⟩ := by
  fin_cases b
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0
