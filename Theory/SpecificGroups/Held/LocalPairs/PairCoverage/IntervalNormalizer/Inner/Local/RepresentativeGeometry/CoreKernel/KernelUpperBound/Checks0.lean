module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound.CheckSupport

/-!
# Checked kernel relations for Held local 0

Two conjugation relations normalize the proposed kernel envelope. The cycle
relation and the six commutation/four braid relations give a complete
six-point stabilizer chain modulo that envelope. Every equality is checked
on all 2058 letters of the original faithful permutation representation.
Source: unchanged ATLAS max3/max4 and HeG1-p2058B0; GLS3 Table 5.3p.
The discovery data are retained in source/small_certificate.json.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound.Checks0
open Held.TwoLocalCandidates
set_option maxRecDepth 8192

public theorem normalize0 :
    generator false 0 * kernelThird false * (generator false 0)⁻¹ = correction false [] 2 := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, representation_generator, representation_third, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem normalize1 :
    generator false 1 * kernelThird false * (generator false 1)⁻¹ = correction false [2, 3, 4] 2 := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, representation_generator, representation_third, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem cycle_relation :
    cycle false = correction false [1, 2, 3, 4, 5] 1 * (((((adjacent false 0 * adjacent false 1) * adjacent false 2) * adjacent false 3) * adjacent false 4)) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_cycle, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute02 :
    adjacent false 0 * adjacent false 2 = correction false [2, 3, 4] 1 * (adjacent false 2 * adjacent false 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute03 :
    adjacent false 0 * adjacent false 3 = correction false [3, 5] 1 * (adjacent false 3 * adjacent false 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute04 :
    adjacent false 0 * adjacent false 4 = correction false [0, 2, 3] 2 * (adjacent false 4 * adjacent false 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute13 :
    adjacent false 1 * adjacent false 3 = correction false [0, 2, 3, 5] 2 * (adjacent false 3 * adjacent false 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute14 :
    adjacent false 1 * adjacent false 4 = correction false [1, 2, 4, 5] 2 * (adjacent false 4 * adjacent false 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute24 :
    adjacent false 2 * adjacent false 4 = correction false [5] 1 * (adjacent false 4 * adjacent false 2) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid0 :
    adjacent false 0 * adjacent false 1 * adjacent false 0 = correction false [0, 2] 0 * (adjacent false 1 * adjacent false 0 * adjacent false 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid1 :
    adjacent false 1 * adjacent false 2 * adjacent false 1 = correction false [0, 3] 0 * (adjacent false 2 * adjacent false 1 * adjacent false 2) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid2 :
    adjacent false 2 * adjacent false 3 * adjacent false 2 = correction false [0, 5] 0 * (adjacent false 3 * adjacent false 2 * adjacent false 3) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid3 :
    adjacent false 3 * adjacent false 4 * adjacent false 3 = correction false [0, 1, 3] 0 * (adjacent false 4 * adjacent false 3 * adjacent false 4) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound.Checks0
