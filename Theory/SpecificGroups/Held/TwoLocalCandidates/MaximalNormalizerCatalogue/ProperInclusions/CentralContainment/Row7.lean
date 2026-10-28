module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

/-!
# Central involution signature in Held row 7

The 8 binary words cover the actual row closure by the checked generator
squares and right transitions. The common word fixes 42 points and has no
partner with 6 common fixed points. Every other binary word either has a
different fixed-point count or has the explicitly selected forbidden partner.
All equalities and counts below are checked by the Lean kernel on the literal
permutation tables; `source/generate.py` only proposes the partner data.

Source: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p;
Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open ProperInclusions

private def partner7 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | _ => 1

set_option maxRecDepth 16384 in
private theorem squares7 : ∀ r : Fin (dim 3),
    rowElement (row 3) r.val * rowElement (row 3) r.val = 1 := by
  apply square_of_table 3
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions7 : ∀ i r,
    normalForm 3 i * rowElement (row 3) r.val = normalForm 3 (flipIndex 3 i r) := by
  apply transition_of_table 3
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count7 : tableCommonCount (normalTable 3 (centralIndex 3))
    (normalTable 3 (centralIndex 3)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem avoids7 : ∀ i, tableCommonCount
    (normalTable 3 (centralIndex 3)) (normalTable 3 i) ≠ bad 3 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem eliminates7 : ∀ i, i = centralIndex 3 ∨
    tableCommonCount (normalTable 3 i) (normalTable 3 i) ≠ 42 ∨
    tableCommonCount (normalTable 3 i) (normalTable 3 (partner7 i)) = bad 3 := by
  decide +kernel

/-- The common word is uniquely determined by the permutation signature in row 7. -/
public theorem row7_signature : Signature 7 6 centralWord ∧
    ∀ x, Signature 7 6 x → x = centralWord :=
  signature_package 3 partner7 squares7 transitions7 count7 avoids7 eliminates7

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
