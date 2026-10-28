module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

/-!
# Central involution signature in Held row 2

The 4 binary words cover the actual row closure by the checked generator
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

private def partner2 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 0

set_option maxRecDepth 16384 in
private theorem squares2 : ∀ r : Fin (dim 0),
    rowElement (row 0) r.val * rowElement (row 0) r.val = 1 := by
  apply square_of_table 0
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions2 : ∀ i r,
    normalForm 0 i * rowElement (row 0) r.val = normalForm 0 (flipIndex 0 i r) := by
  apply transition_of_table 0
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count2 : tableCommonCount (normalTable 0 (centralIndex 0))
    (normalTable 0 (centralIndex 0)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem avoids2 : ∀ i, tableCommonCount
    (normalTable 0 (centralIndex 0)) (normalTable 0 i) ≠ bad 0 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem eliminates2 : ∀ i, i = centralIndex 0 ∨
    tableCommonCount (normalTable 0 i) (normalTable 0 i) ≠ 42 ∨
    tableCommonCount (normalTable 0 i) (normalTable 0 (partner2 i)) = bad 0 := by
  decide +kernel

/-- The common word is uniquely determined by the permutation signature in row 2. -/
public theorem row2_signature : Signature 2 10 centralWord ∧
    ∀ x, Signature 2 10 x → x = centralWord :=
  signature_package 0 partner2 squares2 transitions2 count2 avoids2 eliminates2

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
