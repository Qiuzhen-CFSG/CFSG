module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalVerifier

/-! Kernel-checked adjacent Sylow coset keys, part 1 of five. -/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 1 of 45. -/
theorem keyBlock_00 : KeyBlock 0 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 2 of 45. -/
theorem keyBlock_01 : KeyBlock 1 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 3 of 45. -/
theorem keyBlock_02 : KeyBlock 2 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 4 of 45. -/
theorem keyBlock_03 : KeyBlock 3 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 5 of 45. -/
theorem keyBlock_04 : KeyBlock 4 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 6 of 45. -/
theorem keyBlock_05 : KeyBlock 5 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 7 of 45. -/
theorem keyBlock_06 : KeyBlock 6 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 8 of 45. -/
theorem keyBlock_07 : KeyBlock 7 := by
  apply keyBlock_of_check
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Adjacent coset keys in block 9 of 45. -/
theorem keyBlock_08 : KeyBlock 8 := by
  apply keyBlock_of_check
  decide +kernel

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
