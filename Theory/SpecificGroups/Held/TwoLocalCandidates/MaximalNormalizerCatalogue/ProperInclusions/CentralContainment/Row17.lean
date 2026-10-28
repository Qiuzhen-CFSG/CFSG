module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

import Mathlib.Tactic.FinCases

/-!
# Central involution signature in Held row 17

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

private def partner17 : Fin 16 → Fin 16
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 0
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | _ => 3

set_option maxRecDepth 16384 in
private theorem squares17 : ∀ r : Fin (dim 7),
    rowElement (row 7) r.val * rowElement (row 7) r.val = 1 := by
  apply square_of_table 7
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions17 : ∀ i r,
    normalForm 7 i * rowElement (row 7) r.val = normalForm 7 (flipIndex 7 i r) := by
  apply transition_of_table 7
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count17 : tableCommonCount (normalTable 7 (centralIndex 7))
    (normalTable 7 (centralIndex 7)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_0 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 0) ≠ bad 7 ∧
    ((0 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 0) (normalTable 7 0) ≠ 42 ∨
      tableCommonCount (normalTable 7 0) (normalTable 7 (partner17 0)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_1 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 1) ≠ bad 7 ∧
    ((1 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 1) (normalTable 7 1) ≠ 42 ∨
      tableCommonCount (normalTable 7 1) (normalTable 7 (partner17 1)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_2 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 2) ≠ bad 7 ∧
    ((2 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 2) (normalTable 7 2) ≠ 42 ∨
      tableCommonCount (normalTable 7 2) (normalTable 7 (partner17 2)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_3 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 3) ≠ bad 7 ∧
    ((3 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 3) (normalTable 7 3) ≠ 42 ∨
      tableCommonCount (normalTable 7 3) (normalTable 7 (partner17 3)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_4 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 4) ≠ bad 7 ∧
    ((4 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 4) (normalTable 7 4) ≠ 42 ∨
      tableCommonCount (normalTable 7 4) (normalTable 7 (partner17 4)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_5 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 5) ≠ bad 7 ∧
    ((5 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 5) (normalTable 7 5) ≠ 42 ∨
      tableCommonCount (normalTable 7 5) (normalTable 7 (partner17 5)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_6 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 6) ≠ bad 7 ∧
    ((6 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 6) (normalTable 7 6) ≠ 42 ∨
      tableCommonCount (normalTable 7 6) (normalTable 7 (partner17 6)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_7 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 7) ≠ bad 7 ∧
    ((7 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 7) (normalTable 7 7) ≠ 42 ∨
      tableCommonCount (normalTable 7 7) (normalTable 7 (partner17 7)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_8 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 8) ≠ bad 7 ∧
    ((8 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 8) (normalTable 7 8) ≠ 42 ∨
      tableCommonCount (normalTable 7 8) (normalTable 7 (partner17 8)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_9 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 9) ≠ bad 7 ∧
    ((9 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 9) (normalTable 7 9) ≠ 42 ∨
      tableCommonCount (normalTable 7 9) (normalTable 7 (partner17 9)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_10 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 10) ≠ bad 7 ∧
    ((10 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 10) (normalTable 7 10) ≠ 42 ∨
      tableCommonCount (normalTable 7 10) (normalTable 7 (partner17 10)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_11 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 11) ≠ bad 7 ∧
    ((11 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 11) (normalTable 7 11) ≠ 42 ∨
      tableCommonCount (normalTable 7 11) (normalTable 7 (partner17 11)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_12 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 12) ≠ bad 7 ∧
    ((12 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 12) (normalTable 7 12) ≠ 42 ∨
      tableCommonCount (normalTable 7 12) (normalTable 7 (partner17 12)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_13 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 13) ≠ bad 7 ∧
    ((13 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 13) (normalTable 7 13) ≠ 42 ∨
      tableCommonCount (normalTable 7 13) (normalTable 7 (partner17 13)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_14 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 14) ≠ bad 7 ∧
    ((14 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 14) (normalTable 7 14) ≠ 42 ∨
      tableCommonCount (normalTable 7 14) (normalTable 7 (partner17 14)) = bad 7) := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem signature17_15 :
    tableCommonCount (normalTable 7 (centralIndex 7)) (normalTable 7 15) ≠ bad 7 ∧
    ((15 : Fin (2 ^ dim 7)) = centralIndex 7 ∨
      tableCommonCount (normalTable 7 15) (normalTable 7 15) ≠ 42 ∨
      tableCommonCount (normalTable 7 15) (normalTable 7 (partner17 15)) = bad 7) := by
  decide +kernel

private theorem avoids17 : ∀ i, tableCommonCount
    (normalTable 7 (centralIndex 7)) (normalTable 7 i) ≠ bad 7 := by
  intro i
  fin_cases i
  · exact signature17_0.1
  · exact signature17_1.1
  · exact signature17_2.1
  · exact signature17_3.1
  · exact signature17_4.1
  · exact signature17_5.1
  · exact signature17_6.1
  · exact signature17_7.1
  · exact signature17_8.1
  · exact signature17_9.1
  · exact signature17_10.1
  · exact signature17_11.1
  · exact signature17_12.1
  · exact signature17_13.1
  · exact signature17_14.1
  · exact signature17_15.1

private theorem eliminates17 : ∀ i, i = centralIndex 7 ∨
    tableCommonCount (normalTable 7 i) (normalTable 7 i) ≠ 42 ∨
    tableCommonCount (normalTable 7 i) (normalTable 7 (partner17 i)) = bad 7 := by
  intro i
  fin_cases i
  · exact signature17_0.2
  · exact signature17_1.2
  · exact signature17_2.2
  · exact signature17_3.2
  · exact signature17_4.2
  · exact signature17_5.2
  · exact signature17_6.2
  · exact signature17_7.2
  · exact signature17_8.2
  · exact signature17_9.2
  · exact signature17_10.2
  · exact signature17_11.2
  · exact signature17_12.2
  · exact signature17_13.2
  · exact signature17_14.2
  · exact signature17_15.2

/-- The common word is uniquely determined by the permutation signature in row 17. -/
public theorem row17_signature : Signature 17 10 centralWord ∧
    ∀ x, Signature 17 10 x → x = centralWord :=
  signature_package 7 partner17 squares17 transitions17 count17 avoids17 eliminates17

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
