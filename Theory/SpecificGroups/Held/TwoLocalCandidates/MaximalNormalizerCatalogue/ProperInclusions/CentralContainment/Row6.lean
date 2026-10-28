module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.CentralContainment.FiniteWords

/-!
# Central involution signature in Held row 6

The 8 binary words cover the actual row closure by the checked generator
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

private def partner6 : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | _ => 1

set_option maxRecDepth 16384 in
private theorem squares6 : ∀ r : Fin (dim 2),
    rowElement (row 2) r.val * rowElement (row 2) r.val = 1 := by
  apply square_of_table 2
  decide +kernel

set_option maxRecDepth 16384 in
private theorem transitions6 : ∀ i r,
    normalForm 2 i * rowElement (row 2) r.val = normalForm 2 (flipIndex 2 i r) := by
  apply transition_of_table 2
  decide +kernel

set_option maxRecDepth 16384 in
private theorem count6 : tableCommonCount (normalTable 2 (centralIndex 2))
    (normalTable 2 (centralIndex 2)) = 42 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem avoids6 : ∀ i, tableCommonCount
    (normalTable 2 (centralIndex 2)) (normalTable 2 i) ≠ bad 2 := by decide +kernel

set_option maxRecDepth 16384 in
private theorem eliminates6 : ∀ i, i = centralIndex 2 ∨
    tableCommonCount (normalTable 2 i) (normalTable 2 i) ≠ 42 ∨
    tableCommonCount (normalTable 2 i) (normalTable 2 (partner6 i)) = bad 2 := by
  decide +kernel

/-- The common word is uniquely determined by the permutation signature in row 6. -/
public theorem row6_signature : Signature 6 10 centralWord ∧
    ∀ x, Signature 6 10 x → x = centralWord :=
  signature_package 2 partner6 squares6 transitions6 count6 avoids6 eliminates6

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
