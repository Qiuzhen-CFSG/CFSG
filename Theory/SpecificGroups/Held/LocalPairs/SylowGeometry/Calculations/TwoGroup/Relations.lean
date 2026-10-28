module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
import Mathlib.Tactic.FinCases

/-!
# Certified triangular identities for the Held representative

The ten fourth-power identities and forty-five conjugation identities are
checked on all 2058 letters using tables proved equal to the literal words.
Thus these equations hold in Held.He, independently of any ambient order
or recognition theorem. The conjugation products use only earlier entries.
Source: retained discovery data `TwoGroup/Source/pcRelations.g`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
open Tables Held.TwoLocalCandidates.Cores

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_0 : pcGenerator 0 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_1 : pcGenerator 1 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_2 : pcGenerator 2 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_3 : pcGenerator 3 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_4 : pcGenerator 4 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_5 : pcGenerator 5 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_6 : pcGenerator 6 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_7 : pcGenerator 7 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_8 : pcGenerator 8 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem power_9 : pcGenerator 9 ^ 4 = 1 := by
  apply representation_injective
  rw [map_pow, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem pcGenerator_pow_four (i : Fin 10) : pcGenerator i ^ 4 = 1 := by
  fin_cases i
  · exact power_0
  · exact power_1
  · exact power_2
  · exact power_3
  · exact power_4
  · exact power_5
  · exact power_6
  · exact power_7
  · exact power_8
  · exact power_9

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_1_0 :
    pcGenerator 1 * pcGenerator 0 * (pcGenerator 1)⁻¹ =
      pcProduct (conjugateWord 1 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_2_0 :
    pcGenerator 2 * pcGenerator 0 * (pcGenerator 2)⁻¹ =
      pcProduct (conjugateWord 2 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_2_1 :
    pcGenerator 2 * pcGenerator 1 * (pcGenerator 2)⁻¹ =
      pcProduct (conjugateWord 2 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_3_0 :
    pcGenerator 3 * pcGenerator 0 * (pcGenerator 3)⁻¹ =
      pcProduct (conjugateWord 3 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_3_1 :
    pcGenerator 3 * pcGenerator 1 * (pcGenerator 3)⁻¹ =
      pcProduct (conjugateWord 3 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_3_2 :
    pcGenerator 3 * pcGenerator 2 * (pcGenerator 3)⁻¹ =
      pcProduct (conjugateWord 3 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_4_0 :
    pcGenerator 4 * pcGenerator 0 * (pcGenerator 4)⁻¹ =
      pcProduct (conjugateWord 4 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_4_1 :
    pcGenerator 4 * pcGenerator 1 * (pcGenerator 4)⁻¹ =
      pcProduct (conjugateWord 4 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_4_2 :
    pcGenerator 4 * pcGenerator 2 * (pcGenerator 4)⁻¹ =
      pcProduct (conjugateWord 4 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_4_3 :
    pcGenerator 4 * pcGenerator 3 * (pcGenerator 4)⁻¹ =
      pcProduct (conjugateWord 4 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_5_0 :
    pcGenerator 5 * pcGenerator 0 * (pcGenerator 5)⁻¹ =
      pcProduct (conjugateWord 5 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_5_1 :
    pcGenerator 5 * pcGenerator 1 * (pcGenerator 5)⁻¹ =
      pcProduct (conjugateWord 5 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_5_2 :
    pcGenerator 5 * pcGenerator 2 * (pcGenerator 5)⁻¹ =
      pcProduct (conjugateWord 5 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_5_3 :
    pcGenerator 5 * pcGenerator 3 * (pcGenerator 5)⁻¹ =
      pcProduct (conjugateWord 5 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_5_4 :
    pcGenerator 5 * pcGenerator 4 * (pcGenerator 5)⁻¹ =
      pcProduct (conjugateWord 5 4) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_0 :
    pcGenerator 6 * pcGenerator 0 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_1 :
    pcGenerator 6 * pcGenerator 1 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_2 :
    pcGenerator 6 * pcGenerator 2 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_3 :
    pcGenerator 6 * pcGenerator 3 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_4 :
    pcGenerator 6 * pcGenerator 4 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 4) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_6_5 :
    pcGenerator 6 * pcGenerator 5 * (pcGenerator 6)⁻¹ =
      pcProduct (conjugateWord 6 5) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_0 :
    pcGenerator 7 * pcGenerator 0 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_1 :
    pcGenerator 7 * pcGenerator 1 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_2 :
    pcGenerator 7 * pcGenerator 2 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_3 :
    pcGenerator 7 * pcGenerator 3 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_4 :
    pcGenerator 7 * pcGenerator 4 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 4) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_5 :
    pcGenerator 7 * pcGenerator 5 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 5) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_7_6 :
    pcGenerator 7 * pcGenerator 6 * (pcGenerator 7)⁻¹ =
      pcProduct (conjugateWord 7 6) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_0 :
    pcGenerator 8 * pcGenerator 0 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_1 :
    pcGenerator 8 * pcGenerator 1 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_2 :
    pcGenerator 8 * pcGenerator 2 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_3 :
    pcGenerator 8 * pcGenerator 3 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_4 :
    pcGenerator 8 * pcGenerator 4 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 4) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_5 :
    pcGenerator 8 * pcGenerator 5 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 5) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_6 :
    pcGenerator 8 * pcGenerator 6 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 6) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_8_7 :
    pcGenerator 8 * pcGenerator 7 * (pcGenerator 8)⁻¹ =
      pcProduct (conjugateWord 8 7) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_0 :
    pcGenerator 9 * pcGenerator 0 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 0) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_1 :
    pcGenerator 9 * pcGenerator 1 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 1) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_2 :
    pcGenerator 9 * pcGenerator 2 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 2) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_3 :
    pcGenerator 9 * pcGenerator 3 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 3) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_4 :
    pcGenerator 9 * pcGenerator 4 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 4) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_5 :
    pcGenerator 9 * pcGenerator 5 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 5) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_6 :
    pcGenerator 9 * pcGenerator 6 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 6) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_7 :
    pcGenerator 9 * pcGenerator 7 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 7) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem conjugate_9_8 :
    pcGenerator 9 * pcGenerator 8 * (pcGenerator 9)⁻¹ =
      pcProduct (conjugateWord 9 8) := by
  apply representation_injective
  simp only [pcProduct, conjugateWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, map_mul, map_inv, map_one, ← pcTable_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

/-- Forward conjugation is triangular in the ascending sequence. -/
public theorem pcGenerator_conjugate (k j : Fin 10) (h : j.val < k.val) :
    pcGenerator k * pcGenerator j * (pcGenerator k)⁻¹ =
      pcProduct (conjugateWord k j) := by
  fin_cases k <;> fin_cases j
  · exact False.elim ((by decide : ¬ (0 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (1 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 0) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 0) h)
  · exact conjugate_1_0
  · exact False.elim ((by decide : ¬ (1 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 1) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 1) h)
  · exact conjugate_2_0
  · exact conjugate_2_1
  · exact False.elim ((by decide : ¬ (2 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 2) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 2) h)
  · exact conjugate_3_0
  · exact conjugate_3_1
  · exact conjugate_3_2
  · exact False.elim ((by decide : ¬ (3 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 3) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 3) h)
  · exact conjugate_4_0
  · exact conjugate_4_1
  · exact conjugate_4_2
  · exact conjugate_4_3
  · exact False.elim ((by decide : ¬ (4 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 4) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 4) h)
  · exact conjugate_5_0
  · exact conjugate_5_1
  · exact conjugate_5_2
  · exact conjugate_5_3
  · exact conjugate_5_4
  · exact False.elim ((by decide : ¬ (5 : ℕ) < 5) h)
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 5) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 5) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 5) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 5) h)
  · exact conjugate_6_0
  · exact conjugate_6_1
  · exact conjugate_6_2
  · exact conjugate_6_3
  · exact conjugate_6_4
  · exact conjugate_6_5
  · exact False.elim ((by decide : ¬ (6 : ℕ) < 6) h)
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 6) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 6) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 6) h)
  · exact conjugate_7_0
  · exact conjugate_7_1
  · exact conjugate_7_2
  · exact conjugate_7_3
  · exact conjugate_7_4
  · exact conjugate_7_5
  · exact conjugate_7_6
  · exact False.elim ((by decide : ¬ (7 : ℕ) < 7) h)
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 7) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 7) h)
  · exact conjugate_8_0
  · exact conjugate_8_1
  · exact conjugate_8_2
  · exact conjugate_8_3
  · exact conjugate_8_4
  · exact conjugate_8_5
  · exact conjugate_8_6
  · exact conjugate_8_7
  · exact False.elim ((by decide : ¬ (8 : ℕ) < 8) h)
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 8) h)
  · exact conjugate_9_0
  · exact conjugate_9_1
  · exact conjugate_9_2
  · exact conjugate_9_3
  · exact conjugate_9_4
  · exact conjugate_9_5
  · exact conjugate_9_6
  · exact conjugate_9_7
  · exact conjugate_9_8
  · exact False.elim ((by decide : ¬ (9 : ℕ) < 9) h)

end Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
