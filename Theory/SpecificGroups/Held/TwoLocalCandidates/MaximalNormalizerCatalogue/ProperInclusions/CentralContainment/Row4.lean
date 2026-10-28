module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

/-!
# Central involution signature in Held row 4

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

private def partner4 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | _ => 1

set_option maxRecDepth 16384 in
private theorem squares4 : ∀ r : Fin (dim 1),
    rowElement (row 1) r.val * rowElement (row 1) r.val = 1 := by
  apply square_of_table 1
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions4 : ∀ i r,
    normalForm 1 i * rowElement (row 1) r.val = normalForm 1 (flipIndex 1 i r) := by
  apply transition_of_table 1
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count4 : tableCommonCount (normalTable 1 (centralIndex 1))
    (normalTable 1 (centralIndex 1)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem avoids4 : ∀ i, tableCommonCount
    (normalTable 1 (centralIndex 1)) (normalTable 1 i) ≠ bad 1 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem eliminates4 : ∀ i, i = centralIndex 1 ∨
    tableCommonCount (normalTable 1 i) (normalTable 1 i) ≠ 42 ∨
    tableCommonCount (normalTable 1 i) (normalTable 1 (partner4 i)) = bad 1 := by
  decide +kernel

/-- The common word is uniquely determined by the permutation signature in row 4. -/
public theorem row4_signature : Signature 4 6 centralWord ∧
    ∀ x, Signature 4 6 x → x = centralWord :=
  signature_package 1 partner4 squares4 transitions4 count4 avoids4 eliminates4

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
