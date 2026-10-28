module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.Forest
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion.Tables
import Mathlib.Tactic.FinCases

/-!
# Certified roots of the Held involution fusion forest

For each of the 25 roots, the published concrete conjugator is checked in the
faithful degree-2058 representation. We check `c * r = x * c` on every letter
and cancel `c` to obtain the required conjugation. Packed tables are linked to
the original Held words by proved representation identities.

Source: GLS3 Table 5.3p, interpreted on pp.260–261; the root witnesses in
`Coverage/Source/discovery.json`. `FiniteFusion/Source/generate_checks.py`
prints these checks. The script supplies expressions, not proof oracles.
-/

namespace Held.InvolutionFixedData.Coverage

set_option Elab.async false

open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
open TwoLocalCandidates TwoLocalCandidates.Cores
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open FiniteFusion

private def shiftPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  ((rootShiftWord j).map (fun k =>
    if k.natAbs = 1 then Tables0.p0 ^ k else bTable ^ (if k < 0 then (-1 : ℤ) else 1))).prod

private theorem shiftPerm_eq (j : Fin 25) : representation (rootShift j) = shiftPerm j := by
  simp only [rootShift, shiftPerm, map_list_prod, List.map_map, Function.comp_def,
    apply_ite representation, map_zpow, aTable_eq, bTable_eq]
  rfl

private def refPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  if rootClass j = 0 then Tables0.p0 else Tables2.p2

private theorem refPerm_eq (j : Fin 25) : representation (rootRepresentative j) = refPerm j := by
  simp only [rootRepresentative, refPerm, apply_ite representation, zTable_eq, aTable_eq]
  rfl

private def conjPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  (normalPerm (rootIndex j) * (shiftPerm j * refPerm j * (shiftPerm j)⁻¹)) ^
    (rootHalf j).val * shiftPerm j

private theorem conjPerm_eq (j : Fin 25) : representation (rootConjugator j) = conjPerm j := by
  simp only [rootConjugator, conjPerm, MulAut.conj_apply, map_mul, map_inv,
    map_pow, normalForm_representation, shiftPerm_eq, refPerm_eq]

private theorem allPointsByBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 17, ∀ r : Fin 128,
      P ⟨(q.val * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) : ∀ x, P x := by
  intro x
  have hx := h ⟨x.val / 128, by omega⟩ ⟨x.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : x.val / 128 * 128 + x.val % 128 = x.val := by omega
  simpa only [he, Nat.mod_eq_of_lt x.isLt] using hx

private theorem root_of_check (j : Fin 25)
    (h : conjPerm j * refPerm j = normalPerm (rootIndex j) * conjPerm j) :
    MulAut.conj (rootConjugator j) (rootRepresentative j) =
      (normalForm (rootIndex j)).val := by
  apply representation_injective
  simp only [MulAut.conj_apply, map_mul, map_inv, conjPerm_eq, refPerm_eq,
    normalForm_representation]
  rw [h, mul_inv_cancel_right]

private def rootWord_0 : Equiv.Perm (Fin 2058) :=
  (((c8) * ((bTable * (bTable)) * Tables0.p0 * (bTable * (bTable))⁻¹)) ^ 3 * (bTable * (bTable)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_0 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_1 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_2 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_3 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_4 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_5 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_6 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_7 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_8 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_9 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_10 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_11 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_12 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_13 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_14 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_15 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_0_block_16 : ∀ v : Fin 128,
    (rootWord_0 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8) * rootWord_0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_0 :
    MulAut.conj (rootConjugator 0) (rootRepresentative 0) =
      (normalForm (rootIndex 0)).val := by
  apply root_of_check
  change rootWord_0 * Tables0.p0 = (c8) * rootWord_0
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_0_block_0
  · exact root_0_block_1
  · exact root_0_block_2
  · exact root_0_block_3
  · exact root_0_block_4
  · exact root_0_block_5
  · exact root_0_block_6
  · exact root_0_block_7
  · exact root_0_block_8
  · exact root_0_block_9
  · exact root_0_block_10
  · exact root_0_block_11
  · exact root_0_block_12
  · exact root_0_block_13
  · exact root_0_block_14
  · exact root_0_block_15
  · exact root_0_block_16

private def rootWord_1 : Equiv.Perm (Fin 2058) :=
  (((c9 * (c8)) * ((bTable) * Tables0.p0 * (bTable)⁻¹)) ^ 2 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_0 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_1 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_2 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_3 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_4 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_5 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_6 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_7 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_8 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_9 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_10 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_11 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_12 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_13 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_14 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_15 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_1_block_16 : ∀ v : Fin 128,
    (rootWord_1 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8)) * rootWord_1) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_1 :
    MulAut.conj (rootConjugator 1) (rootRepresentative 1) =
      (normalForm (rootIndex 1)).val := by
  apply root_of_check
  change rootWord_1 * Tables0.p0 = (c9 * (c8)) * rootWord_1
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_1_block_0
  · exact root_1_block_1
  · exact root_1_block_2
  · exact root_1_block_3
  · exact root_1_block_4
  · exact root_1_block_5
  · exact root_1_block_6
  · exact root_1_block_7
  · exact root_1_block_8
  · exact root_1_block_9
  · exact root_1_block_10
  · exact root_1_block_11
  · exact root_1_block_12
  · exact root_1_block_13
  · exact root_1_block_14
  · exact root_1_block_15
  · exact root_1_block_16

private def rootWord_2 : Equiv.Perm (Fin 2058) :=
  (((c7) * ((bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0)))))))))))) * Tables0.p0 * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0))))))))))))⁻¹)) ^ 2 * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0)))))))))))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_0 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_1 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_2 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_3 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_4 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_5 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_6 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_7 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_8 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_9 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_10 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_11 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_12 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_13 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_14 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_15 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_2_block_16 : ∀ v : Fin 128,
    (rootWord_2 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7) * rootWord_2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_2 :
    MulAut.conj (rootConjugator 2) (rootRepresentative 2) =
      (normalForm (rootIndex 2)).val := by
  apply root_of_check
  change rootWord_2 * Tables0.p0 = (c7) * rootWord_2
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_2_block_0
  · exact root_2_block_1
  · exact root_2_block_2
  · exact root_2_block_3
  · exact root_2_block_4
  · exact root_2_block_5
  · exact root_2_block_6
  · exact root_2_block_7
  · exact root_2_block_8
  · exact root_2_block_9
  · exact root_2_block_10
  · exact root_2_block_11
  · exact root_2_block_12
  · exact root_2_block_13
  · exact root_2_block_14
  · exact root_2_block_15
  · exact root_2_block_16

private def rootWord_3 : Equiv.Perm (Fin 2058) :=
  (((c8 * (c7)) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 9 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_0 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_1 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_2 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_3 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_4 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_5 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_6 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_7 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_8 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_9 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_10 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_11 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_12 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_13 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_14 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_15 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_3_block_16 : ∀ v : Fin 128,
    (rootWord_3 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c7)) * rootWord_3) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_3 :
    MulAut.conj (rootConjugator 3) (rootRepresentative 3) =
      (normalForm (rootIndex 3)).val := by
  apply root_of_check
  change rootWord_3 * Tables2.p2 = (c8 * (c7)) * rootWord_3
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_3_block_0
  · exact root_3_block_1
  · exact root_3_block_2
  · exact root_3_block_3
  · exact root_3_block_4
  · exact root_3_block_5
  · exact root_3_block_6
  · exact root_3_block_7
  · exact root_3_block_8
  · exact root_3_block_9
  · exact root_3_block_10
  · exact root_3_block_11
  · exact root_3_block_12
  · exact root_3_block_13
  · exact root_3_block_14
  · exact root_3_block_15
  · exact root_3_block_16

private def rootWord_4 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c6)) * ((bTable * (bTable)) * Tables2.p2 * (bTable * (bTable))⁻¹)) ^ 9 * (bTable * (bTable)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_0 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_1 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_2 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_3 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_4 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_5 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_6 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_7 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_8 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_9 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_10 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_11 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_12 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_13 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_14 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_15 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_4_block_16 : ∀ v : Fin 128,
    (rootWord_4 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6)) * rootWord_4) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_4 :
    MulAut.conj (rootConjugator 4) (rootRepresentative 4) =
      (normalForm (rootIndex 4)).val := by
  apply root_of_check
  change rootWord_4 * Tables2.p2 = (c7 * (c6)) * rootWord_4
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_4_block_0
  · exact root_4_block_1
  · exact root_4_block_2
  · exact root_4_block_3
  · exact root_4_block_4
  · exact root_4_block_5
  · exact root_4_block_6
  · exact root_4_block_7
  · exact root_4_block_8
  · exact root_4_block_9
  · exact root_4_block_10
  · exact root_4_block_11
  · exact root_4_block_12
  · exact root_4_block_13
  · exact root_4_block_14
  · exact root_4_block_15
  · exact root_4_block_16

private def rootWord_5 : Equiv.Perm (Fin 2058) :=
  (((c5) * ((bTable * (bTable)) * Tables0.p0 * (bTable * (bTable))⁻¹)) ^ 2 * (bTable * (bTable)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_0 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_1 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_2 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_3 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_4 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_5 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_6 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_7 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_8 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_9 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_10 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_11 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_12 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_13 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_14 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_15 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_5_block_16 : ∀ v : Fin 128,
    (rootWord_5 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5) * rootWord_5) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_5 :
    MulAut.conj (rootConjugator 5) (rootRepresentative 5) =
      (normalForm (rootIndex 5)).val := by
  apply root_of_check
  change rootWord_5 * Tables0.p0 = (c5) * rootWord_5
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_5_block_0
  · exact root_5_block_1
  · exact root_5_block_2
  · exact root_5_block_3
  · exact root_5_block_4
  · exact root_5_block_5
  · exact root_5_block_6
  · exact root_5_block_7
  · exact root_5_block_8
  · exact root_5_block_9
  · exact root_5_block_10
  · exact root_5_block_11
  · exact root_5_block_12
  · exact root_5_block_13
  · exact root_5_block_14
  · exact root_5_block_15
  · exact root_5_block_16

private def rootWord_6 : Equiv.Perm (Fin 2058) :=
  (((c8 * (c4)) * ((1) * Tables0.p0 * (1)⁻¹)) ^ 2 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_0 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_1 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_2 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_3 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_4 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_5 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_6 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_7 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_8 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_9 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_10 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_11 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_12 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_13 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_14 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_15 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_6_block_16 : ∀ v : Fin 128,
    (rootWord_6 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4)) * rootWord_6) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_6 :
    MulAut.conj (rootConjugator 6) (rootRepresentative 6) =
      (normalForm (rootIndex 6)).val := by
  apply root_of_check
  change rootWord_6 * Tables0.p0 = (c8 * (c4)) * rootWord_6
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_6_block_0
  · exact root_6_block_1
  · exact root_6_block_2
  · exact root_6_block_3
  · exact root_6_block_4
  · exact root_6_block_5
  · exact root_6_block_6
  · exact root_6_block_7
  · exact root_6_block_8
  · exact root_6_block_9
  · exact root_6_block_10
  · exact root_6_block_11
  · exact root_6_block_12
  · exact root_6_block_13
  · exact root_6_block_14
  · exact root_6_block_15
  · exact root_6_block_16

private def rootWord_7 : Equiv.Perm (Fin 2058) :=
  (((c5 * (c4)) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 8 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_0 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_1 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_2 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_3 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_4 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_5 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_6 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_7 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_8 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_9 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_10 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_11 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_12 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_13 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_14 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_15 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_7_block_16 : ∀ v : Fin 128,
    (rootWord_7 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4)) * rootWord_7) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_7 :
    MulAut.conj (rootConjugator 7) (rootRepresentative 7) =
      (normalForm (rootIndex 7)).val := by
  apply root_of_check
  change rootWord_7 * Tables2.p2 = (c5 * (c4)) * rootWord_7
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_7_block_0
  · exact root_7_block_1
  · exact root_7_block_2
  · exact root_7_block_3
  · exact root_7_block_4
  · exact root_7_block_5
  · exact root_7_block_6
  · exact root_7_block_7
  · exact root_7_block_8
  · exact root_7_block_9
  · exact root_7_block_10
  · exact root_7_block_11
  · exact root_7_block_12
  · exact root_7_block_13
  · exact root_7_block_14
  · exact root_7_block_15
  · exact root_7_block_16

private def rootWord_8 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c5 * (c4))) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 9 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_0 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_1 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_2 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_3 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_4 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_5 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_6 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_7 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_8 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_9 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_10 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_11 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_12 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_13 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_14 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_15 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_8_block_16 : ∀ v : Fin 128,
    (rootWord_8 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4))) * rootWord_8) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_8 :
    MulAut.conj (rootConjugator 8) (rootRepresentative 8) =
      (normalForm (rootIndex 8)).val := by
  apply root_of_check
  change rootWord_8 * Tables2.p2 = (c7 * (c5 * (c4))) * rootWord_8
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_8_block_0
  · exact root_8_block_1
  · exact root_8_block_2
  · exact root_8_block_3
  · exact root_8_block_4
  · exact root_8_block_5
  · exact root_8_block_6
  · exact root_8_block_7
  · exact root_8_block_8
  · exact root_8_block_9
  · exact root_8_block_10
  · exact root_8_block_11
  · exact root_8_block_12
  · exact root_8_block_13
  · exact root_8_block_14
  · exact root_8_block_15
  · exact root_8_block_16

private def rootWord_9 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c6 * (c5 * (c4)))) * ((bTable⁻¹ * (bTable⁻¹ * (bTable⁻¹))) * Tables2.p2 * (bTable⁻¹ * (bTable⁻¹ * (bTable⁻¹)))⁻¹)) ^ 9 * (bTable⁻¹ * (bTable⁻¹ * (bTable⁻¹))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_0 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_1 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_2 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_3 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_4 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_5 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_6 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_7 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_8 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_9 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_10 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_11 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_12 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_13 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_14 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_15 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_9_block_16 : ∀ v : Fin 128,
    (rootWord_9 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4)))) * rootWord_9) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_9 :
    MulAut.conj (rootConjugator 9) (rootRepresentative 9) =
      (normalForm (rootIndex 9)).val := by
  apply root_of_check
  change rootWord_9 * Tables2.p2 = (c7 * (c6 * (c5 * (c4)))) * rootWord_9
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_9_block_0
  · exact root_9_block_1
  · exact root_9_block_2
  · exact root_9_block_3
  · exact root_9_block_4
  · exact root_9_block_5
  · exact root_9_block_6
  · exact root_9_block_7
  · exact root_9_block_8
  · exact root_9_block_9
  · exact root_9_block_10
  · exact root_9_block_11
  · exact root_9_block_12
  · exact root_9_block_13
  · exact root_9_block_14
  · exact root_9_block_15
  · exact root_9_block_16

private def rootWord_10 : Equiv.Perm (Fin 2058) :=
  (((c9 * (c7 * (c6 * (c3)))) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 11 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_0 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_1 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_2 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_3 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_4 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_5 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_6 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_7 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_8 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_9 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_10 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_11 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_12 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_13 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_14 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_15 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_10_block_16 : ∀ v : Fin 128,
    (rootWord_10 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c7 * (c6 * (c3)))) * rootWord_10) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_10 :
    MulAut.conj (rootConjugator 10) (rootRepresentative 10) =
      (normalForm (rootIndex 10)).val := by
  apply root_of_check
  change rootWord_10 * Tables2.p2 = (c9 * (c7 * (c6 * (c3)))) * rootWord_10
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_10_block_0
  · exact root_10_block_1
  · exact root_10_block_2
  · exact root_10_block_3
  · exact root_10_block_4
  · exact root_10_block_5
  · exact root_10_block_6
  · exact root_10_block_7
  · exact root_10_block_8
  · exact root_10_block_9
  · exact root_10_block_10
  · exact root_10_block_11
  · exact root_10_block_12
  · exact root_10_block_13
  · exact root_10_block_14
  · exact root_10_block_15
  · exact root_10_block_16

private def rootWord_11 : Equiv.Perm (Fin 2058) :=
  (((c4 * (c3)) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 8 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_0 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_1 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_2 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_3 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_4 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_5 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_6 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_7 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_8 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_9 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_10 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_11 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_12 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_13 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_14 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_15 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_11_block_16 : ∀ v : Fin 128,
    (rootWord_11 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3)) * rootWord_11) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_11 :
    MulAut.conj (rootConjugator 11) (rootRepresentative 11) =
      (normalForm (rootIndex 11)).val := by
  apply root_of_check
  change rootWord_11 * Tables2.p2 = (c4 * (c3)) * rootWord_11
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_11_block_0
  · exact root_11_block_1
  · exact root_11_block_2
  · exact root_11_block_3
  · exact root_11_block_4
  · exact root_11_block_5
  · exact root_11_block_6
  · exact root_11_block_7
  · exact root_11_block_8
  · exact root_11_block_9
  · exact root_11_block_10
  · exact root_11_block_11
  · exact root_11_block_12
  · exact root_11_block_13
  · exact root_11_block_14
  · exact root_11_block_15
  · exact root_11_block_16

private def rootWord_12 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c6 * (c4 * (c3)))) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 9 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_0 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_1 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_2 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_3 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_4 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_5 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_6 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_7 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_8 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_9 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_10 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_11 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_12 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_13 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_14 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_15 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_12_block_16 : ∀ v : Fin 128,
    (rootWord_12 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c4 * (c3)))) * rootWord_12) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_12 :
    MulAut.conj (rootConjugator 12) (rootRepresentative 12) =
      (normalForm (rootIndex 12)).val := by
  apply root_of_check
  change rootWord_12 * Tables2.p2 = (c7 * (c6 * (c4 * (c3)))) * rootWord_12
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_12_block_0
  · exact root_12_block_1
  · exact root_12_block_2
  · exact root_12_block_3
  · exact root_12_block_4
  · exact root_12_block_5
  · exact root_12_block_6
  · exact root_12_block_7
  · exact root_12_block_8
  · exact root_12_block_9
  · exact root_12_block_10
  · exact root_12_block_11
  · exact root_12_block_12
  · exact root_12_block_13
  · exact root_12_block_14
  · exact root_12_block_15
  · exact root_12_block_16

private def rootWord_13 : Equiv.Perm (Fin 2058) :=
  (((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 9 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_0 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_1 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_2 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_3 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_4 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_5 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_6 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_7 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_8 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_9 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_10 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_11 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_12 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_13 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_14 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_15 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_13_block_16 : ∀ v : Fin 128,
    (rootWord_13 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_13 :
    MulAut.conj (rootConjugator 13) (rootRepresentative 13) =
      (normalForm (rootIndex 13)).val := by
  apply root_of_check
  change rootWord_13 * Tables2.p2 = (c9 * (c8 * (c7 * (c6 * (c4 * (c3)))))) * rootWord_13
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_13_block_0
  · exact root_13_block_1
  · exact root_13_block_2
  · exact root_13_block_3
  · exact root_13_block_4
  · exact root_13_block_5
  · exact root_13_block_6
  · exact root_13_block_7
  · exact root_13_block_8
  · exact root_13_block_9
  · exact root_13_block_10
  · exact root_13_block_11
  · exact root_13_block_12
  · exact root_13_block_13
  · exact root_13_block_14
  · exact root_13_block_15
  · exact root_13_block_16

private def rootWord_14 : Equiv.Perm (Fin 2058) :=
  (((c5 * (c2)) * ((Tables0.p0 * (bTable * (bTable⁻¹ * (Tables0.p0 * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable)))))))))))) * Tables0.p0 * (Tables0.p0 * (bTable * (bTable⁻¹ * (Tables0.p0 * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable))))))))))))⁻¹)) ^ 2 * (Tables0.p0 * (bTable * (bTable⁻¹ * (Tables0.p0 * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable * (Tables0.p0 * (Tables0.p0 * (bTable⁻¹ * (bTable)))))))))))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_0 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_1 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_2 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_3 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_4 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_5 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_6 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_7 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_8 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_9 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_10 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_11 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_12 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_13 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_14 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_15 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_14_block_16 : ∀ v : Fin 128,
    (rootWord_14 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c2)) * rootWord_14) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_14 :
    MulAut.conj (rootConjugator 14) (rootRepresentative 14) =
      (normalForm (rootIndex 14)).val := by
  apply root_of_check
  change rootWord_14 * Tables0.p0 = (c5 * (c2)) * rootWord_14
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_14_block_0
  · exact root_14_block_1
  · exact root_14_block_2
  · exact root_14_block_3
  · exact root_14_block_4
  · exact root_14_block_5
  · exact root_14_block_6
  · exact root_14_block_7
  · exact root_14_block_8
  · exact root_14_block_9
  · exact root_14_block_10
  · exact root_14_block_11
  · exact root_14_block_12
  · exact root_14_block_13
  · exact root_14_block_14
  · exact root_14_block_15
  · exact root_14_block_16

private def rootWord_15 : Equiv.Perm (Fin 2058) :=
  (((c4 * (c2)) * ((bTable⁻¹ * (bTable⁻¹ * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹)))))))))))) * Tables0.p0 * (bTable⁻¹ * (bTable⁻¹ * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹))))))))))))⁻¹)) ^ 3 * (bTable⁻¹ * (bTable⁻¹ * (bTable * (bTable⁻¹ * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹ * (Tables0.p0 * (bTable * (Tables0.p0 * (bTable⁻¹ * (bTable⁻¹)))))))))))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_0 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_1 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_2 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_3 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_4 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_5 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_6 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_7 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_8 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_9 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_10 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_11 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_12 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_13 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_14 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_15 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_15_block_16 : ∀ v : Fin 128,
    (rootWord_15 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c2)) * rootWord_15) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_15 :
    MulAut.conj (rootConjugator 15) (rootRepresentative 15) =
      (normalForm (rootIndex 15)).val := by
  apply root_of_check
  change rootWord_15 * Tables0.p0 = (c4 * (c2)) * rootWord_15
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_15_block_0
  · exact root_15_block_1
  · exact root_15_block_2
  · exact root_15_block_3
  · exact root_15_block_4
  · exact root_15_block_5
  · exact root_15_block_6
  · exact root_15_block_7
  · exact root_15_block_8
  · exact root_15_block_9
  · exact root_15_block_10
  · exact root_15_block_11
  · exact root_15_block_12
  · exact root_15_block_13
  · exact root_15_block_14
  · exact root_15_block_15
  · exact root_15_block_16

private def rootWord_16 : Equiv.Perm (Fin 2058) :=
  (((c8 * (c4 * (c2))) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 8 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_0 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_1 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_2 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_3 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_4 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_5 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_6 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_7 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_8 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_9 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_10 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_11 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_12 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_13 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_14 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_15 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_16_block_16 : ∀ v : Fin 128,
    (rootWord_16 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c4 * (c2))) * rootWord_16) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_16 :
    MulAut.conj (rootConjugator 16) (rootRepresentative 16) =
      (normalForm (rootIndex 16)).val := by
  apply root_of_check
  change rootWord_16 * Tables2.p2 = (c8 * (c4 * (c2))) * rootWord_16
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_16_block_0
  · exact root_16_block_1
  · exact root_16_block_2
  · exact root_16_block_3
  · exact root_16_block_4
  · exact root_16_block_5
  · exact root_16_block_6
  · exact root_16_block_7
  · exact root_16_block_8
  · exact root_16_block_9
  · exact root_16_block_10
  · exact root_16_block_11
  · exact root_16_block_12
  · exact root_16_block_13
  · exact root_16_block_14
  · exact root_16_block_15
  · exact root_16_block_16

private def rootWord_17 : Equiv.Perm (Fin 2058) :=
  (((c8 * (c5 * (c3 * (c2)))) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 9 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_0 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_1 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_2 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_3 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_4 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_5 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_6 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_7 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_8 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_9 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_10 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_11 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_12 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_13 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_14 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_15 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_17_block_16 : ∀ v : Fin 128,
    (rootWord_17 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c8 * (c5 * (c3 * (c2)))) * rootWord_17) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_17 :
    MulAut.conj (rootConjugator 17) (rootRepresentative 17) =
      (normalForm (rootIndex 17)).val := by
  apply root_of_check
  change rootWord_17 * Tables2.p2 = (c8 * (c5 * (c3 * (c2)))) * rootWord_17
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_17_block_0
  · exact root_17_block_1
  · exact root_17_block_2
  · exact root_17_block_3
  · exact root_17_block_4
  · exact root_17_block_5
  · exact root_17_block_6
  · exact root_17_block_7
  · exact root_17_block_8
  · exact root_17_block_9
  · exact root_17_block_10
  · exact root_17_block_11
  · exact root_17_block_12
  · exact root_17_block_13
  · exact root_17_block_14
  · exact root_17_block_15
  · exact root_17_block_16

private def rootWord_18 : Equiv.Perm (Fin 2058) :=
  (((c5 * (c4 * (c3 * (c2)))) * ((bTable) * Tables0.p0 * (bTable)⁻¹)) ^ 3 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_0 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_1 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_2 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_3 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_4 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_5 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_6 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_7 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_8 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_9 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_10 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_11 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_12 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_13 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_14 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_15 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_18_block_16 : ∀ v : Fin 128,
    (rootWord_18 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c2)))) * rootWord_18) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_18 :
    MulAut.conj (rootConjugator 18) (rootRepresentative 18) =
      (normalForm (rootIndex 18)).val := by
  apply root_of_check
  change rootWord_18 * Tables0.p0 = (c5 * (c4 * (c3 * (c2)))) * rootWord_18
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_18_block_0
  · exact root_18_block_1
  · exact root_18_block_2
  · exact root_18_block_3
  · exact root_18_block_4
  · exact root_18_block_5
  · exact root_18_block_6
  · exact root_18_block_7
  · exact root_18_block_8
  · exact root_18_block_9
  · exact root_18_block_10
  · exact root_18_block_11
  · exact root_18_block_12
  · exact root_18_block_13
  · exact root_18_block_14
  · exact root_18_block_15
  · exact root_18_block_16

private def rootWord_19 : Equiv.Perm (Fin 2058) :=
  (((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * ((1) * Tables2.p2 * (1)⁻¹)) ^ 9 * (1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_0 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_1 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_2 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_3 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_4 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_5 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_6 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_7 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_8 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_9 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_10 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_11 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_12 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_13 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_14 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_15 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_19_block_16 : ∀ v : Fin 128,
    (rootWord_19 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_19 :
    MulAut.conj (rootConjugator 19) (rootRepresentative 19) =
      (normalForm (rootIndex 19)).val := by
  apply root_of_check
  change rootWord_19 * Tables2.p2 = (c9 * (c8 * (c7 * (c6 * (c5 * (c4 * (c3 * (c2)))))))) * rootWord_19
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_19_block_0
  · exact root_19_block_1
  · exact root_19_block_2
  · exact root_19_block_3
  · exact root_19_block_4
  · exact root_19_block_5
  · exact root_19_block_6
  · exact root_19_block_7
  · exact root_19_block_8
  · exact root_19_block_9
  · exact root_19_block_10
  · exact root_19_block_11
  · exact root_19_block_12
  · exact root_19_block_13
  · exact root_19_block_14
  · exact root_19_block_15
  · exact root_19_block_16

private def rootWord_20 : Equiv.Perm (Fin 2058) :=
  (((c5 * (c4 * (c3 * (c1)))) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 9 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_0 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_1 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_2 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_3 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_4 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_5 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_6 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_7 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_8 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_9 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_10 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_11 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_12 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_13 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_14 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_15 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_20_block_16 : ∀ v : Fin 128,
    (rootWord_20 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c5 * (c4 * (c3 * (c1)))) * rootWord_20) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_20 :
    MulAut.conj (rootConjugator 20) (rootRepresentative 20) =
      (normalForm (rootIndex 20)).val := by
  apply root_of_check
  change rootWord_20 * Tables2.p2 = (c5 * (c4 * (c3 * (c1)))) * rootWord_20
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_20_block_0
  · exact root_20_block_1
  · exact root_20_block_2
  · exact root_20_block_3
  · exact root_20_block_4
  · exact root_20_block_5
  · exact root_20_block_6
  · exact root_20_block_7
  · exact root_20_block_8
  · exact root_20_block_9
  · exact root_20_block_10
  · exact root_20_block_11
  · exact root_20_block_12
  · exact root_20_block_13
  · exact root_20_block_14
  · exact root_20_block_15
  · exact root_20_block_16

private def rootWord_21 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c5 * (c4 * (c3 * (c1))))) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 11 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_0 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_1 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_2 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_3 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_4 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_5 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_6 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_7 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_8 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_9 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_10 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_11 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_12 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_13 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_14 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_15 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_21_block_16 : ∀ v : Fin 128,
    (rootWord_21 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_21 :
    MulAut.conj (rootConjugator 21) (rootRepresentative 21) =
      (normalForm (rootIndex 21)).val := by
  apply root_of_check
  change rootWord_21 * Tables2.p2 = (c7 * (c5 * (c4 * (c3 * (c1))))) * rootWord_21
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_21_block_0
  · exact root_21_block_1
  · exact root_21_block_2
  · exact root_21_block_3
  · exact root_21_block_4
  · exact root_21_block_5
  · exact root_21_block_6
  · exact root_21_block_7
  · exact root_21_block_8
  · exact root_21_block_9
  · exact root_21_block_10
  · exact root_21_block_11
  · exact root_21_block_12
  · exact root_21_block_13
  · exact root_21_block_14
  · exact root_21_block_15
  · exact root_21_block_16

private def rootWord_22 : Equiv.Perm (Fin 2058) :=
  (((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * ((bTable⁻¹ * (bTable⁻¹)) * Tables0.p0 * (bTable⁻¹ * (bTable⁻¹))⁻¹)) ^ 2 * (bTable⁻¹ * (bTable⁻¹)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_0 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_1 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_2 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_3 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_4 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_5 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_6 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_7 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_8 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_9 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_10 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_11 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_12 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_13 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_14 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_15 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_22_block_16 : ∀ v : Fin 128,
    (rootWord_22 * Tables0.p0) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_22 :
    MulAut.conj (rootConjugator 22) (rootRepresentative 22) =
      (normalForm (rootIndex 22)).val := by
  apply root_of_check
  change rootWord_22 * Tables0.p0 = (c7 * (c6 * (c5 * (c4 * (c3 * (c1)))))) * rootWord_22
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_22_block_0
  · exact root_22_block_1
  · exact root_22_block_2
  · exact root_22_block_3
  · exact root_22_block_4
  · exact root_22_block_5
  · exact root_22_block_6
  · exact root_22_block_7
  · exact root_22_block_8
  · exact root_22_block_9
  · exact root_22_block_10
  · exact root_22_block_11
  · exact root_22_block_12
  · exact root_22_block_13
  · exact root_22_block_14
  · exact root_22_block_15
  · exact root_22_block_16

private def rootWord_23 : Equiv.Perm (Fin 2058) :=
  (((c4 * (c3 * (c2 * (c1)))) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 9 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_0 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_1 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_2 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_3 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_4 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_5 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_6 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_7 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_8 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_9 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_10 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_11 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_12 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_13 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_14 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_15 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_23_block_16 : ∀ v : Fin 128,
    (rootWord_23 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c4 * (c3 * (c2 * (c1)))) * rootWord_23) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_23 :
    MulAut.conj (rootConjugator 23) (rootRepresentative 23) =
      (normalForm (rootIndex 23)).val := by
  apply root_of_check
  change rootWord_23 * Tables2.p2 = (c4 * (c3 * (c2 * (c1)))) * rootWord_23
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_23_block_0
  · exact root_23_block_1
  · exact root_23_block_2
  · exact root_23_block_3
  · exact root_23_block_4
  · exact root_23_block_5
  · exact root_23_block_6
  · exact root_23_block_7
  · exact root_23_block_8
  · exact root_23_block_9
  · exact root_23_block_10
  · exact root_23_block_11
  · exact root_23_block_12
  · exact root_23_block_13
  · exact root_23_block_14
  · exact root_23_block_15
  · exact root_23_block_16

private def rootWord_24 : Equiv.Perm (Fin 2058) :=
  (((c0) * ((bTable) * Tables2.p2 * (bTable)⁻¹)) ^ 8 * (bTable))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_0 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(0 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_1 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(1 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_2 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(2 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_3 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(3 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_4 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(4 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_5 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(5 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_6 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(6 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_7 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(7 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_8 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(8 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_9 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(9 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_10 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(10 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_11 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(11 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_12 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(12 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_13 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(13 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_14 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(14 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_15 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(15 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem root_24_block_16 : ∀ v : Fin 128,
    (rootWord_24 * Tables2.p2) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ((c0) * rootWord_24) ⟨(16 * 128 + v.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem root_24 :
    MulAut.conj (rootConjugator 24) (rootRepresentative 24) =
      (normalForm (rootIndex 24)).val := by
  apply root_of_check
  change rootWord_24 * Tables2.p2 = (c0) * rootWord_24
  apply Equiv.ext
  apply allPointsByBlocks
  intro q
  fin_cases q
  · exact root_24_block_0
  · exact root_24_block_1
  · exact root_24_block_2
  · exact root_24_block_3
  · exact root_24_block_4
  · exact root_24_block_5
  · exact root_24_block_6
  · exact root_24_block_7
  · exact root_24_block_8
  · exact root_24_block_9
  · exact root_24_block_10
  · exact root_24_block_11
  · exact root_24_block_12
  · exact root_24_block_13
  · exact root_24_block_14
  · exact root_24_block_15
  · exact root_24_block_16

/-- Each of the 25 roots is the claimed conjugate of its literal representative. -/
public theorem root_conjugation_identity (j : Fin 25) :
    MulAut.conj (rootConjugator j) (rootRepresentative j) =
      (normalForm (rootIndex j)).val := by
  fin_cases j
  · exact root_0
  · exact root_1
  · exact root_2
  · exact root_3
  · exact root_4
  · exact root_5
  · exact root_6
  · exact root_7
  · exact root_8
  · exact root_9
  · exact root_10
  · exact root_11
  · exact root_12
  · exact root_13
  · exact root_14
  · exact root_15
  · exact root_16
  · exact root_17
  · exact root_18
  · exact root_19
  · exact root_20
  · exact root_21
  · exact root_22
  · exact root_23
  · exact root_24

end Held.InvolutionFixedData.Coverage
