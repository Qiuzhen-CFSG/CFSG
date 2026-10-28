module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

import Mathlib.Tactic.FinCases

/-!
# Central involution signature in Held row 13

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

private def partner13 : Fin 16 → Fin 16
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
private theorem squares13 : ∀ r : Fin (dim 4),
    rowElement (row 4) r.val * rowElement (row 4) r.val = 1 := by
  apply square_of_table 4
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions13 : ∀ i r,
    normalForm 4 i * rowElement (row 4) r.val = normalForm 4 (flipIndex 4 i r) := by
  apply transition_of_table 4
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count13 : tableCommonCount (normalTable 4 (centralIndex 4))
    (normalTable 4 (centralIndex 4)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_0 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 0) ≠ bad 4 ∧
    ((0 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 0) (normalTable 4 0) ≠ 42 ∨
      tableCommonCount (normalTable 4 0) (normalTable 4 (partner13 0)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_1 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 1) ≠ bad 4 ∧
    ((1 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 1) (normalTable 4 1) ≠ 42 ∨
      tableCommonCount (normalTable 4 1) (normalTable 4 (partner13 1)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_2 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 2) ≠ bad 4 ∧
    ((2 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 2) (normalTable 4 2) ≠ 42 ∨
      tableCommonCount (normalTable 4 2) (normalTable 4 (partner13 2)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_3 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 3) ≠ bad 4 ∧
    ((3 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 3) (normalTable 4 3) ≠ 42 ∨
      tableCommonCount (normalTable 4 3) (normalTable 4 (partner13 3)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_4 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 4) ≠ bad 4 ∧
    ((4 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 4) (normalTable 4 4) ≠ 42 ∨
      tableCommonCount (normalTable 4 4) (normalTable 4 (partner13 4)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_5 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 5) ≠ bad 4 ∧
    ((5 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 5) (normalTable 4 5) ≠ 42 ∨
      tableCommonCount (normalTable 4 5) (normalTable 4 (partner13 5)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_6 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 6) ≠ bad 4 ∧
    ((6 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 6) (normalTable 4 6) ≠ 42 ∨
      tableCommonCount (normalTable 4 6) (normalTable 4 (partner13 6)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_7 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 7) ≠ bad 4 ∧
    ((7 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 7) (normalTable 4 7) ≠ 42 ∨
      tableCommonCount (normalTable 4 7) (normalTable 4 (partner13 7)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_8 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 8) ≠ bad 4 ∧
    ((8 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 8) (normalTable 4 8) ≠ 42 ∨
      tableCommonCount (normalTable 4 8) (normalTable 4 (partner13 8)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_9 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 9) ≠ bad 4 ∧
    ((9 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 9) (normalTable 4 9) ≠ 42 ∨
      tableCommonCount (normalTable 4 9) (normalTable 4 (partner13 9)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_10 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 10) ≠ bad 4 ∧
    ((10 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 10) (normalTable 4 10) ≠ 42 ∨
      tableCommonCount (normalTable 4 10) (normalTable 4 (partner13 10)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_11 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 11) ≠ bad 4 ∧
    ((11 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 11) (normalTable 4 11) ≠ 42 ∨
      tableCommonCount (normalTable 4 11) (normalTable 4 (partner13 11)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_12 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 12) ≠ bad 4 ∧
    ((12 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 12) (normalTable 4 12) ≠ 42 ∨
      tableCommonCount (normalTable 4 12) (normalTable 4 (partner13 12)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_13 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 13) ≠ bad 4 ∧
    ((13 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 13) (normalTable 4 13) ≠ 42 ∨
      tableCommonCount (normalTable 4 13) (normalTable 4 (partner13 13)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_14 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 14) ≠ bad 4 ∧
    ((14 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 14) (normalTable 4 14) ≠ 42 ∨
      tableCommonCount (normalTable 4 14) (normalTable 4 (partner13 14)) = bad 4) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature13_15 :
    tableCommonCount (normalTable 4 (centralIndex 4)) (normalTable 4 15) ≠ bad 4 ∧
    ((15 : Fin (2 ^ dim 4)) = centralIndex 4 ∨
      tableCommonCount (normalTable 4 15) (normalTable 4 15) ≠ 42 ∨
      tableCommonCount (normalTable 4 15) (normalTable 4 (partner13 15)) = bad 4) := by
  decide +kernel

private theorem avoids13 : ∀ i, tableCommonCount
    (normalTable 4 (centralIndex 4)) (normalTable 4 i) ≠ bad 4 := by
  intro i
  fin_cases i
  · exact signature13_0.1
  · exact signature13_1.1
  · exact signature13_2.1
  · exact signature13_3.1
  · exact signature13_4.1
  · exact signature13_5.1
  · exact signature13_6.1
  · exact signature13_7.1
  · exact signature13_8.1
  · exact signature13_9.1
  · exact signature13_10.1
  · exact signature13_11.1
  · exact signature13_12.1
  · exact signature13_13.1
  · exact signature13_14.1
  · exact signature13_15.1

private theorem eliminates13 : ∀ i, i = centralIndex 4 ∨
    tableCommonCount (normalTable 4 i) (normalTable 4 i) ≠ 42 ∨
    tableCommonCount (normalTable 4 i) (normalTable 4 (partner13 i)) = bad 4 := by
  intro i
  fin_cases i
  · exact signature13_0.2
  · exact signature13_1.2
  · exact signature13_2.2
  · exact signature13_3.2
  · exact signature13_4.2
  · exact signature13_5.2
  · exact signature13_6.2
  · exact signature13_7.2
  · exact signature13_8.2
  · exact signature13_9.2
  · exact signature13_10.2
  · exact signature13_11.2
  · exact signature13_12.2
  · exact signature13_13.2
  · exact signature13_14.2
  · exact signature13_15.2

/-- The common word is uniquely determined by the permutation signature in row 13. -/
public theorem row13_signature : Signature 13 10 centralWord ∧
    ∀ x, Signature 13 10 x → x = centralWord :=
  signature_package 4 partner13 squares13 transitions13 count13 avoids13 eliminates13

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
