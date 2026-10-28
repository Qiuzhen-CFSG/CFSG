module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables1
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.CollectionWords
import Mathlib.Tactic.FinCases

/-!
# Checked power and conjugation identities for Held candidate 1

All equations hold in the actual local subgroup. They are checked as
permutations of all 2058 letters, using tables already proved equal to the
literal ATLAS words. These identities establish the triangular two-group
series and invariance under the two local generators.
Source: GLS3 Table 5.3p; retained ATLAS degree-2058 permutations.
-/

namespace Held.TwoLocalCandidates.Cores
open Tables1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_0 : coreGenerator 1 0 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_1 : coreGenerator 1 1 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_2 : coreGenerator 1 2 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p4_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_3 : coreGenerator 1 3 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p5_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_4 : coreGenerator 1 4 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p6_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_5 : coreGenerator 1 5 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p7_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_6 : coreGenerator 1 6 ^ 4 = 1 := by
  apply embedding_injective 1
  rw [map_pow, map_one, ← p8_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem powers1 (j : Fin 7) : coreGenerator 1 j ^ 4 = 1 := by
  fin_cases j
  · exact power_0
  · exact power_1
  · exact power_2
  · exact power_3
  · exact power_4
  · exact power_5
  · exact power_6

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_1_0 :
    coreGenerator 1 1 * coreGenerator 1 0 * (coreGenerator 1 1)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 1 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_2_0 :
    coreGenerator 1 2 * coreGenerator 1 0 * (coreGenerator 1 2)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 2 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p4_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_2_1 :
    coreGenerator 1 2 * coreGenerator 1 1 * (coreGenerator 1 2)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 2 1 then 1 else 0) *
        coreGenerator 1 1 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p4_eq, ← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_3_0 :
    coreGenerator 1 3 * coreGenerator 1 0 * (coreGenerator 1 3)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 3 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p5_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_3_1 :
    coreGenerator 1 3 * coreGenerator 1 1 * (coreGenerator 1 3)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 3 1 then 1 else 0) *
        coreGenerator 1 1 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p5_eq, ← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_3_2 :
    coreGenerator 1 3 * coreGenerator 1 2 * (coreGenerator 1 3)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 3 2 then 1 else 0) *
        coreGenerator 1 2 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p5_eq, ← p4_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_4_0 :
    coreGenerator 1 4 * coreGenerator 1 0 * (coreGenerator 1 4)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 4 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p6_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_4_1 :
    coreGenerator 1 4 * coreGenerator 1 1 * (coreGenerator 1 4)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 4 1 then 1 else 0) *
        coreGenerator 1 1 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p6_eq, ← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_4_2 :
    coreGenerator 1 4 * coreGenerator 1 2 * (coreGenerator 1 4)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 4 2 then 1 else 0) *
        coreGenerator 1 2 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p6_eq, ← p4_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_4_3 :
    coreGenerator 1 4 * coreGenerator 1 3 * (coreGenerator 1 4)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 4 3 then 1 else 0) *
        coreGenerator 1 3 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p6_eq, ← p5_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_5_0 :
    coreGenerator 1 5 * coreGenerator 1 0 * (coreGenerator 1 5)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 5 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p7_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_5_1 :
    coreGenerator 1 5 * coreGenerator 1 1 * (coreGenerator 1 5)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 5 1 then 1 else 0) *
        coreGenerator 1 1 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p7_eq, ← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_5_2 :
    coreGenerator 1 5 * coreGenerator 1 2 * (coreGenerator 1 5)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 5 2 then 1 else 0) *
        coreGenerator 1 2 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p7_eq, ← p4_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_5_3 :
    coreGenerator 1 5 * coreGenerator 1 3 * (coreGenerator 1 5)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 5 3 then 1 else 0) *
        coreGenerator 1 3 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p7_eq, ← p5_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_5_4 :
    coreGenerator 1 5 * coreGenerator 1 4 * (coreGenerator 1 5)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 5 4 then 1 else 0) *
        coreGenerator 1 4 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p7_eq, ← p6_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_0 :
    coreGenerator 1 6 * coreGenerator 1 0 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 0 then 1 else 0) *
        coreGenerator 1 0 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_1 :
    coreGenerator 1 6 * coreGenerator 1 1 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 1 then 1 else 0) *
        coreGenerator 1 1 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p3_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_2 :
    coreGenerator 1 6 * coreGenerator 1 2 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 2 then 1 else 0) *
        coreGenerator 1 2 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p4_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_3 :
    coreGenerator 1 6 * coreGenerator 1 3 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 3 then 1 else 0) *
        coreGenerator 1 3 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p5_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_4 :
    coreGenerator 1 6 * coreGenerator 1 4 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 4 then 1 else 0) *
        coreGenerator 1 4 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p6_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem internal_6_5 :
    coreGenerator 1 6 * coreGenerator 1 5 * (coreGenerator 1 6)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 6 5 then 1 else 0) *
        coreGenerator 1 5 := by
  apply embedding_injective 1
  simp only [map_mul, map_inv, map_pow]
  rw [← p8_eq, ← p7_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem internalConjugation1 (k j : Fin 7) (h : j.val < k.val) :
    coreGenerator 1 k * coreGenerator 1 j * (coreGenerator 1 k)⁻¹ =
      coreGenerator 1 0 ^ (if commutatorBit 1 k j then 1 else 0) *
        coreGenerator 1 j := by
  fin_cases k <;> fin_cases j
  · exact False.elim ((by decide : ¬ (0 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (1 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 0) h)
  · exact internal_1_0
  · exact False.elim ((by decide : ¬ (1 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 1) h)
  · exact internal_2_0
  · exact internal_2_1
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 2) h)
  · exact internal_3_0
  · exact internal_3_1
  · exact internal_3_2
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 3) h)
  · exact internal_4_0
  · exact internal_4_1
  · exact internal_4_2
  · exact internal_4_3
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 4) h)
  · exact internal_5_0
  · exact internal_5_1
  · exact internal_5_2
  · exact internal_5_3
  · exact internal_5_4
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 5) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 5) h)
  · exact internal_6_0
  · exact internal_6_1
  · exact internal_6_2
  · exact internal_6_3
  · exact internal_6_4
  · exact internal_6_5
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 6) h)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_0 :
    localGenerator 1 0 * coreGenerator 1 0 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 0) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p2_eq, ← p3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_1 :
    localGenerator 1 0 * coreGenerator 1 1 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 1) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p2_eq, ← p3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_2 :
    localGenerator 1 0 * coreGenerator 1 2 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 2) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p4_eq, ← p5_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_3 :
    localGenerator 1 0 * coreGenerator 1 3 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 3) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p4_eq, ← p5_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_4 :
    localGenerator 1 0 * coreGenerator 1 4 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 4) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p2_eq, ← p3_eq, ← p4_eq, ← p5_eq, ← p6_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_5 :
    localGenerator 1 0 * coreGenerator 1 5 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 5) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p3_eq, ← p5_eq, ← p6_eq, ← p7_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_0_6 :
    localGenerator 1 0 * coreGenerator 1 6 * (localGenerator 1 0)⁻¹ =
      coreProduct 1 (conjugateWord 1 0 6) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p0_eq, ← p8_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_0 :
    localGenerator 1 1 * coreGenerator 1 0 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 0) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p2_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_1 :
    localGenerator 1 1 * coreGenerator 1 1 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 1) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p3_eq, ← p4_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_2 :
    localGenerator 1 1 * coreGenerator 1 2 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 2) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p2_eq, ← p3_eq, ← p4_eq, ← p5_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_3 :
    localGenerator 1 1 * coreGenerator 1 3 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 3) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p5_eq, ← p6_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_4 :
    localGenerator 1 1 * coreGenerator 1 4 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 4) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p6_eq, ← p7_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_5 :
    localGenerator 1 1 * coreGenerator 1 5 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 5) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_cons, List.prod_cons, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p2_eq, ← p4_eq, ← p5_eq, ← p7_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem local_1_6 :
    localGenerator 1 1 * coreGenerator 1 6 * (localGenerator 1 1)⁻¹ =
      coreProduct 1 (conjugateWord 1 1 6) := by
  apply embedding_injective 1
  simp only [coreProduct, conjugateWord, List.map_nil,
    List.prod_nil, map_mul, map_inv, map_one, ← p1_eq, ← p8_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem localConjugation1 (k : Fin 2) (j : Fin 7) :
    localGenerator 1 k * coreGenerator 1 j * (localGenerator 1 k)⁻¹ =
      coreProduct 1 (conjugateWord 1 k j) := by
  fin_cases k <;> fin_cases j
  · exact local_0_0
  · exact local_0_1
  · exact local_0_2
  · exact local_0_3
  · exact local_0_4
  · exact local_0_5
  · exact local_0_6
  · exact local_1_0
  · exact local_1_1
  · exact local_1_2
  · exact local_1_3
  · exact local_1_4
  · exact local_1_5
  · exact local_1_6

end Held.TwoLocalCandidates.Cores
