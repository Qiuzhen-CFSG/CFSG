module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound.CheckSupport

/-!
# Checked kernel relations for Held local 1

Two conjugation relations normalize the proposed kernel envelope. The cycle
relation and the six commutation/four braid relations give a complete
six-point stabilizer chain modulo that envelope. Every equality is checked
on all 2058 letters of the original faithful permutation representation.
Source: unchanged ATLAS max3/max4 and HeG1-p2058B0; GLS3 Table 5.3p.
The discovery data are retained in source/small_certificate.json.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound.Checks1
open Held.TwoLocalCandidates
set_option maxRecDepth 8192

public theorem normalize0 :
    generator true 0 * kernelThird true * (generator true 0)⁻¹ = correction true [2] 2 := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, representation_generator, representation_third, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem normalize1 :
    generator true 1 * kernelThird true * (generator true 1)⁻¹ = correction true [1, 2, 5] 1 := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, representation_generator, representation_third, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem cycle_relation :
    cycle true = correction true [3, 5] 0 * (((((adjacent true 0 * adjacent true 1) * adjacent true 2) * adjacent true 3) * adjacent true 4)) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_cycle, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute02 :
    adjacent true 0 * adjacent true 2 = correction true [0, 1, 3, 4] 1 * (adjacent true 2 * adjacent true 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute03 :
    adjacent true 0 * adjacent true 3 = correction true [] 0 * (adjacent true 3 * adjacent true 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute04 :
    adjacent true 0 * adjacent true 4 = correction true [3, 4] 2 * (adjacent true 4 * adjacent true 0) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute13 :
    adjacent true 1 * adjacent true 3 = correction true [3, 4] 2 * (adjacent true 3 * adjacent true 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute14 :
    adjacent true 1 * adjacent true 4 = correction true [] 0 * (adjacent true 4 * adjacent true 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem commute24 :
    adjacent true 2 * adjacent true 4 = correction true [2, 3, 4] 1 * (adjacent true 4 * adjacent true 2) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid0 :
    adjacent true 0 * adjacent true 1 * adjacent true 0 = correction true [] 0 * (adjacent true 1 * adjacent true 0 * adjacent true 1) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid1 :
    adjacent true 1 * adjacent true 2 * adjacent true 1 = correction true [] 0 * (adjacent true 2 * adjacent true 1 * adjacent true 2) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid2 :
    adjacent true 2 * adjacent true 3 * adjacent true 2 = correction true [] 0 * (adjacent true 3 * adjacent true 2 * adjacent true 3) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

public theorem braid3 :
    adjacent true 3 * adjacent true 4 * adjacent true 3 = correction true [] 0 * (adjacent true 4 * adjacent true 3 * adjacent true 4) := by
  apply Subtype.val_injective
  apply representation_injective
  simp only [Subgroup.coe_mul, map_mul, representation_adjacent_table, representation_correction]
  apply Equiv.ext
  apply Cores.allLetters
  decide +kernel

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound.Checks1
