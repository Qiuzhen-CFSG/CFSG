module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

import Mathlib.Tactic.FinCases

/-!
# Central involution signature in Held row 14

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

private def partner14 : Fin 16 → Fin 16
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
private theorem squares14 : ∀ r : Fin (dim 5),
    rowElement (row 5) r.val * rowElement (row 5) r.val = 1 := by
  apply square_of_table 5
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions14 : ∀ i r,
    normalForm 5 i * rowElement (row 5) r.val = normalForm 5 (flipIndex 5 i r) := by
  apply transition_of_table 5
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count14 : tableCommonCount (normalTable 5 (centralIndex 5))
    (normalTable 5 (centralIndex 5)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_0 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 0) ≠ bad 5 ∧
    ((0 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 0) (normalTable 5 0) ≠ 42 ∨
      tableCommonCount (normalTable 5 0) (normalTable 5 (partner14 0)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_1 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 1) ≠ bad 5 ∧
    ((1 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 1) (normalTable 5 1) ≠ 42 ∨
      tableCommonCount (normalTable 5 1) (normalTable 5 (partner14 1)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_2 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 2) ≠ bad 5 ∧
    ((2 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 2) (normalTable 5 2) ≠ 42 ∨
      tableCommonCount (normalTable 5 2) (normalTable 5 (partner14 2)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_3 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 3) ≠ bad 5 ∧
    ((3 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 3) (normalTable 5 3) ≠ 42 ∨
      tableCommonCount (normalTable 5 3) (normalTable 5 (partner14 3)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_4 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 4) ≠ bad 5 ∧
    ((4 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 4) (normalTable 5 4) ≠ 42 ∨
      tableCommonCount (normalTable 5 4) (normalTable 5 (partner14 4)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_5 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 5) ≠ bad 5 ∧
    ((5 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 5) (normalTable 5 5) ≠ 42 ∨
      tableCommonCount (normalTable 5 5) (normalTable 5 (partner14 5)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_6 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 6) ≠ bad 5 ∧
    ((6 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 6) (normalTable 5 6) ≠ 42 ∨
      tableCommonCount (normalTable 5 6) (normalTable 5 (partner14 6)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_7 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 7) ≠ bad 5 ∧
    ((7 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 7) (normalTable 5 7) ≠ 42 ∨
      tableCommonCount (normalTable 5 7) (normalTable 5 (partner14 7)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_8 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 8) ≠ bad 5 ∧
    ((8 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 8) (normalTable 5 8) ≠ 42 ∨
      tableCommonCount (normalTable 5 8) (normalTable 5 (partner14 8)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_9 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 9) ≠ bad 5 ∧
    ((9 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 9) (normalTable 5 9) ≠ 42 ∨
      tableCommonCount (normalTable 5 9) (normalTable 5 (partner14 9)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_10 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 10) ≠ bad 5 ∧
    ((10 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 10) (normalTable 5 10) ≠ 42 ∨
      tableCommonCount (normalTable 5 10) (normalTable 5 (partner14 10)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_11 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 11) ≠ bad 5 ∧
    ((11 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 11) (normalTable 5 11) ≠ 42 ∨
      tableCommonCount (normalTable 5 11) (normalTable 5 (partner14 11)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_12 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 12) ≠ bad 5 ∧
    ((12 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 12) (normalTable 5 12) ≠ 42 ∨
      tableCommonCount (normalTable 5 12) (normalTable 5 (partner14 12)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_13 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 13) ≠ bad 5 ∧
    ((13 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 13) (normalTable 5 13) ≠ 42 ∨
      tableCommonCount (normalTable 5 13) (normalTable 5 (partner14 13)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_14 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 14) ≠ bad 5 ∧
    ((14 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 14) (normalTable 5 14) ≠ 42 ∨
      tableCommonCount (normalTable 5 14) (normalTable 5 (partner14 14)) = bad 5) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature14_15 :
    tableCommonCount (normalTable 5 (centralIndex 5)) (normalTable 5 15) ≠ bad 5 ∧
    ((15 : Fin (2 ^ dim 5)) = centralIndex 5 ∨
      tableCommonCount (normalTable 5 15) (normalTable 5 15) ≠ 42 ∨
      tableCommonCount (normalTable 5 15) (normalTable 5 (partner14 15)) = bad 5) := by
  decide +kernel

private theorem avoids14 : ∀ i, tableCommonCount
    (normalTable 5 (centralIndex 5)) (normalTable 5 i) ≠ bad 5 := by
  intro i
  fin_cases i
  · exact signature14_0.1
  · exact signature14_1.1
  · exact signature14_2.1
  · exact signature14_3.1
  · exact signature14_4.1
  · exact signature14_5.1
  · exact signature14_6.1
  · exact signature14_7.1
  · exact signature14_8.1
  · exact signature14_9.1
  · exact signature14_10.1
  · exact signature14_11.1
  · exact signature14_12.1
  · exact signature14_13.1
  · exact signature14_14.1
  · exact signature14_15.1

private theorem eliminates14 : ∀ i, i = centralIndex 5 ∨
    tableCommonCount (normalTable 5 i) (normalTable 5 i) ≠ 42 ∨
    tableCommonCount (normalTable 5 i) (normalTable 5 (partner14 i)) = bad 5 := by
  intro i
  fin_cases i
  · exact signature14_0.2
  · exact signature14_1.2
  · exact signature14_2.2
  · exact signature14_3.2
  · exact signature14_4.2
  · exact signature14_5.2
  · exact signature14_6.2
  · exact signature14_7.2
  · exact signature14_8.2
  · exact signature14_9.2
  · exact signature14_10.2
  · exact signature14_11.2
  · exact signature14_12.2
  · exact signature14_13.2
  · exact signature14_14.2
  · exact signature14_15.2

/-- The common word is uniquely determined by the permutation signature in row 14. -/
public theorem row14_signature : Signature 14 10 centralWord ∧
    ∀ x, Signature 14 10 x → x = centralWord :=
  signature_package 5 partner14 squares14 transitions14 count14 avoids14 eliminates14

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
