module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

import Mathlib.Tactic.FinCases

/-!
# Central involution signature in Held row 15

The 16 binary words cover the actual row closure by the checked generator
squares and right transitions. The common word fixes 42 points and has no
partner with 10 common fixed points. Every other binary word either has a
different fixed-point count or has the explicitly selected forbidden partner.
All equalities and counts below are checked by the Lean kernel on the literal
permutation tables; `source/generate.py` only proposes the partner data.

Source: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p;
Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open ProperInclusions

set_option Elab.async false

private def partner15 : Fin 16 → Fin 16
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 0
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | _ => 2

set_option maxRecDepth 16384 in
private theorem squares15 : ∀ r : Fin (dim 6),
    rowElement (row 6) r.val * rowElement (row 6) r.val = 1 := by
  apply square_of_table 6
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions15 : ∀ i r,
    normalForm 6 i * rowElement (row 6) r.val = normalForm 6 (flipIndex 6 i r) := by
  apply transition_of_table 6
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count15 : tableCommonCount (normalTable 6 (centralIndex 6))
    (normalTable 6 (centralIndex 6)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_0 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 0) ≠ bad 6 ∧
    ((0 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 0) (normalTable 6 0) ≠ 42 ∨
      tableCommonCount (normalTable 6 0) (normalTable 6 (partner15 0)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_1 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 1) ≠ bad 6 ∧
    ((1 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 1) (normalTable 6 1) ≠ 42 ∨
      tableCommonCount (normalTable 6 1) (normalTable 6 (partner15 1)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_2 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 2) ≠ bad 6 ∧
    ((2 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 2) (normalTable 6 2) ≠ 42 ∨
      tableCommonCount (normalTable 6 2) (normalTable 6 (partner15 2)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_3 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 3) ≠ bad 6 ∧
    ((3 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 3) (normalTable 6 3) ≠ 42 ∨
      tableCommonCount (normalTable 6 3) (normalTable 6 (partner15 3)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_4 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 4) ≠ bad 6 ∧
    ((4 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 4) (normalTable 6 4) ≠ 42 ∨
      tableCommonCount (normalTable 6 4) (normalTable 6 (partner15 4)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_5 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 5) ≠ bad 6 ∧
    ((5 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 5) (normalTable 6 5) ≠ 42 ∨
      tableCommonCount (normalTable 6 5) (normalTable 6 (partner15 5)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_6 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 6) ≠ bad 6 ∧
    ((6 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 6) (normalTable 6 6) ≠ 42 ∨
      tableCommonCount (normalTable 6 6) (normalTable 6 (partner15 6)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_7 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 7) ≠ bad 6 ∧
    ((7 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 7) (normalTable 6 7) ≠ 42 ∨
      tableCommonCount (normalTable 6 7) (normalTable 6 (partner15 7)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_8 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 8) ≠ bad 6 ∧
    ((8 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 8) (normalTable 6 8) ≠ 42 ∨
      tableCommonCount (normalTable 6 8) (normalTable 6 (partner15 8)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_9 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 9) ≠ bad 6 ∧
    ((9 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 9) (normalTable 6 9) ≠ 42 ∨
      tableCommonCount (normalTable 6 9) (normalTable 6 (partner15 9)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_10 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 10) ≠ bad 6 ∧
    ((10 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 10) (normalTable 6 10) ≠ 42 ∨
      tableCommonCount (normalTable 6 10) (normalTable 6 (partner15 10)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_11 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 11) ≠ bad 6 ∧
    ((11 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 11) (normalTable 6 11) ≠ 42 ∨
      tableCommonCount (normalTable 6 11) (normalTable 6 (partner15 11)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_12 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 12) ≠ bad 6 ∧
    ((12 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 12) (normalTable 6 12) ≠ 42 ∨
      tableCommonCount (normalTable 6 12) (normalTable 6 (partner15 12)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_13 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 13) ≠ bad 6 ∧
    ((13 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 13) (normalTable 6 13) ≠ 42 ∨
      tableCommonCount (normalTable 6 13) (normalTable 6 (partner15 13)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_14 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 14) ≠ bad 6 ∧
    ((14 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 14) (normalTable 6 14) ≠ 42 ∨
      tableCommonCount (normalTable 6 14) (normalTable 6 (partner15 14)) = bad 6) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature15_15 :
    tableCommonCount (normalTable 6 (centralIndex 6)) (normalTable 6 15) ≠ bad 6 ∧
    ((15 : Fin (2 ^ dim 6)) = centralIndex 6 ∨
      tableCommonCount (normalTable 6 15) (normalTable 6 15) ≠ 42 ∨
      tableCommonCount (normalTable 6 15) (normalTable 6 (partner15 15)) = bad 6) := by
  decide +kernel

private theorem avoids15 : ∀ i, tableCommonCount
    (normalTable 6 (centralIndex 6)) (normalTable 6 i) ≠ bad 6 := by
  intro i
  fin_cases i
  · exact signature15_0.1
  · exact signature15_1.1
  · exact signature15_2.1
  · exact signature15_3.1
  · exact signature15_4.1
  · exact signature15_5.1
  · exact signature15_6.1
  · exact signature15_7.1
  · exact signature15_8.1
  · exact signature15_9.1
  · exact signature15_10.1
  · exact signature15_11.1
  · exact signature15_12.1
  · exact signature15_13.1
  · exact signature15_14.1
  · exact signature15_15.1

private theorem eliminates15 : ∀ i, i = centralIndex 6 ∨
    tableCommonCount (normalTable 6 i) (normalTable 6 i) ≠ 42 ∨
    tableCommonCount (normalTable 6 i) (normalTable 6 (partner15 i)) = bad 6 := by
  intro i
  fin_cases i
  · exact signature15_0.2
  · exact signature15_1.2
  · exact signature15_2.2
  · exact signature15_3.2
  · exact signature15_4.2
  · exact signature15_5.2
  · exact signature15_6.2
  · exact signature15_7.2
  · exact signature15_8.2
  · exact signature15_9.2
  · exact signature15_10.2
  · exact signature15_11.2
  · exact signature15_12.2
  · exact signature15_13.2
  · exact signature15_14.2
  · exact signature15_15.2

/-- The common word is uniquely determined by the permutation signature in row 15. -/
public theorem row15_signature : Signature 15 10 centralWord ∧
    ∀ x, Signature 15 10 x → x = centralWord :=
  signature_package 6 partner15 squares15 transitions15 count15 avoids15 eliminates15

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
