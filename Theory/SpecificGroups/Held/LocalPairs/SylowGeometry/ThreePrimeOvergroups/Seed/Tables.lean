module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed.Words
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed.Permutations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tables identified with the eight exact Held seed words

The checked short-prefix equations assemble to each literal word. Mapping
through the defining representation avoids reduction of subgroup membership
proofs. The resulting permutation API supports the two-group and reachability
certificates. Source: ATLAS HeG1-p2058B0 and `Seed/Source/`.
-/

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed

set_option maxRecDepth 2048 in
private theorem representation_seed_0 : representation (seedGenerator 0) = atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g0_eq : g0 = representation (seedGenerator 0) := by
  rw [representation_seed_0]
  rw [g0_step, g0_stage6_step, g0_stage5_step, g0_stage4_step, g0_stage3_step, g0_stage2_step, g0_stage1_step, g0_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_1 : representation (seedGenerator 1) = atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB * atlasA * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB * atlasA * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ ^ 3 * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ ^ 3 * atlasB⁻¹ ^ 5 * atlasA⁻¹ * atlasB⁻¹ ^ 4 * atlasA⁻¹ * atlasB⁻¹ := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g1_eq : g1 = representation (seedGenerator 1) := by
  rw [representation_seed_1]
  rw [g1_step, g1_stage18_step, g1_stage17_step, g1_stage16_step, g1_stage15_step, g1_stage14_step, g1_stage13_step, g1_stage12_step, g1_stage11_step, g1_stage10_step, g1_stage9_step, g1_stage8_step, g1_stage7_step, g1_stage6_step, g1_stage5_step, g1_stage4_step, g1_stage3_step, g1_stage2_step, g1_stage1_step, g1_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_2 : representation (seedGenerator 2) = atlasA⁻¹ * atlasB⁻¹ * atlasA * atlasB * atlasA * atlasB⁻¹ * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA * atlasB⁻¹ * atlasA * atlasB ^ 2 * atlasA * atlasB⁻¹ * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g2_eq : g2 = representation (seedGenerator 2) := by
  rw [representation_seed_2]
  rw [g2_step, g2_stage8_step, g2_stage7_step, g2_stage6_step, g2_stage5_step, g2_stage4_step, g2_stage3_step, g2_stage2_step, g2_stage1_step, g2_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_3 : representation (seedGenerator 3) = atlasB ^ 5 * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB ^ 3 * atlasA * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 2 * atlasA * atlasB := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g3_eq : g3 = representation (seedGenerator 3) := by
  rw [representation_seed_3]
  rw [g3_step, g3_stage9_step, g3_stage8_step, g3_stage7_step, g3_stage6_step, g3_stage5_step, g3_stage4_step, g3_stage3_step, g3_stage2_step, g3_stage1_step, g3_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_4 : representation (seedGenerator 4) = atlasB⁻¹ * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 2 * atlasA * atlasB⁻¹ * atlasA * atlasB ^ 2 * atlasA * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 5 := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g4_eq : g4 = representation (seedGenerator 4) := by
  rw [representation_seed_4]
  rw [g4_step, g4_stage12_step, g4_stage11_step, g4_stage10_step, g4_stage9_step, g4_stage8_step, g4_stage7_step, g4_stage6_step, g4_stage5_step, g4_stage4_step, g4_stage3_step, g4_stage2_step, g4_stage1_step, g4_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_5 : representation (seedGenerator 5) = atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 3 * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB⁻¹ ^ 3 * atlasA * atlasB * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB * atlasA * atlasB⁻¹ * atlasA * atlasB ^ 2 * atlasA * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ * atlasA * atlasB * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g5_eq : g5 = representation (seedGenerator 5) := by
  rw [representation_seed_5]
  rw [g5_step, g5_stage10_step, g5_stage9_step, g5_stage8_step, g5_stage7_step, g5_stage6_step, g5_stage5_step, g5_stage4_step, g5_stage3_step, g5_stage2_step, g5_stage1_step, g5_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_6 : representation (seedGenerator 6) = atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g6_eq : g6 = representation (seedGenerator 6) := by
  rw [representation_seed_6]
  rw [g6_step, g6_stage4_step, g6_stage3_step, g6_stage2_step, g6_stage1_step, g6_stage0_step, packedA_eq, packedB_eq]

set_option maxRecDepth 2048 in
private theorem representation_seed_7 : representation (seedGenerator 7) = atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 3 * atlasA * atlasB * atlasA * atlasB⁻¹ ^ 3 * atlasA * atlasB * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 2 * atlasA * atlasB⁻¹ ^ 2 * atlasA * atlasB ^ 2 * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA * atlasB⁻¹ * atlasA * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB * atlasA * atlasB * atlasA * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB * atlasA * atlasB ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ ^ 3 * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB * atlasA * atlasB⁻¹ ^ 3 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA * atlasB * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ ^ 3 * atlasB⁻¹ ^ 2 * atlasA⁻¹ ^ 2 * atlasB ^ 2 * atlasA⁻¹ * atlasB⁻¹ ^ 2 * atlasA⁻¹ * atlasB⁻¹ * atlasA⁻¹ * atlasB⁻¹ := by
  norm_num only [seedGenerator]
  rfl

set_option maxRecDepth 2048 in
public theorem g7_eq : g7 = representation (seedGenerator 7) := by
  rw [representation_seed_7]
  rw [g7_step, g7_stage18_step, g7_stage17_step, g7_stage16_step, g7_stage15_step, g7_stage14_step, g7_stage13_step, g7_stage12_step, g7_stage11_step, g7_stage10_step, g7_stage9_step, g7_stage8_step, g7_stage7_step, g7_stage6_step, g7_stage5_step, g7_stage4_step, g7_stage3_step, g7_stage2_step, g7_stage1_step, g7_stage0_step, packedA_eq, packedB_eq]

@[expose] public def seedTable : Fin 8 → Equiv.Perm (Fin 2058)
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | 3 => g3
  | 4 => g4
  | 5 => g5
  | 6 => g6
  | 7 => g7

public theorem seedTable_eq (i : Fin 8) : seedTable i = representation (seedGenerator i) := by
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq
  · exact g4_eq
  · exact g5_eq
  · exact g6_eq
  · exact g7_eq

@[expose] public def pcTable : Fin 10 → Equiv.Perm (Fin 2058)
  | 0 => (seedTable 0)⁻¹
  | 1 => (seedTable 5)⁻¹ * seedTable 0 * seedTable 5
  | 2 => (seedTable 1)⁻¹ * (seedTable 0)⁻¹
  | 3 => seedTable 2 * (seedTable 0)⁻¹
  | 4 => (seedTable 6)⁻¹
  | 5 => (seedTable 3)⁻¹ * (seedTable 3)⁻¹
  | 6 => seedTable 3 * (seedTable 0)⁻¹
  | 7 => (seedTable 5)⁻¹ * seedTable 3 * seedTable 5
  | 8 => (seedTable 4)⁻¹ * (seedTable 0)⁻¹
  | 9 => (seedTable 5)⁻¹

public theorem pcTable_eq (i : Fin 10) : pcTable i = representation (pcGenerator i) := by
  fin_cases i <;> simp only [pcTable, pcGenerator, map_mul, map_inv, seedTable_eq]

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed
