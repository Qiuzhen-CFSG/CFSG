module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00TwoData
import Mathlib.Tactic.FinCases

/-!
# Checked cyclic-series power and conjugation relations

The literal ATLAS degree-2058 action certifies every identity by kernel
reduction in bounded blocks. No numerical GAP output is a proof premise.
Sources: HeG1-p2058B0, max3/max4 programs, and LocalActions/source/Explore.g.
Reproduction: Factors/source/generate.py; proposed series: ../source/pcdata.json.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

abbrev power_4_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 ^ relativeOrder 4) x = ((powerWord 4).map pcTable).prod x

private theorem power_4_action_block0 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem power_4_action_block1 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem power_4_action_block2 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem power_4_action_block3 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem power_4_action_block4 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem power_4_action_block5 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem power_4_action_block6 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem power_4_action_block7 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem power_4_action_block8 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem power_4_action_block9 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem power_4_action_block10 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem power_4_action_block11 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem power_4_action_block12 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem power_4_action_block13 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem power_4_action_block14 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem power_4_action_block15 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem power_4_action_block16 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem power_4_action_block17 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem power_4_action_block18 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem power_4_action_block19 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem power_4_action_block20 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem power_4_action_block21 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem power_4_action_block22 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem power_4_action_block23 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem power_4_action_block24 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem power_4_action_block25 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem power_4_action_block26 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem power_4_action_block27 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem power_4_action_block28 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem power_4_action_block29 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem power_4_action_block30 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem power_4_action_block31 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem power_4_action_block32 : checkFin 64 (fun j => decide (power_4_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem power_4_action : ∀ x, power_4_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ power_4_action_block0
  · exact allFin _ _ power_4_action_block1
  · exact allFin _ _ power_4_action_block2
  · exact allFin _ _ power_4_action_block3
  · exact allFin _ _ power_4_action_block4
  · exact allFin _ _ power_4_action_block5
  · exact allFin _ _ power_4_action_block6
  · exact allFin _ _ power_4_action_block7
  · exact allFin _ _ power_4_action_block8
  · exact allFin _ _ power_4_action_block9
  · exact allFin _ _ power_4_action_block10
  · exact allFin _ _ power_4_action_block11
  · exact allFin _ _ power_4_action_block12
  · exact allFin _ _ power_4_action_block13
  · exact allFin _ _ power_4_action_block14
  · exact allFin _ _ power_4_action_block15
  · exact allFin _ _ power_4_action_block16
  · exact allFin _ _ power_4_action_block17
  · exact allFin _ _ power_4_action_block18
  · exact allFin _ _ power_4_action_block19
  · exact allFin _ _ power_4_action_block20
  · exact allFin _ _ power_4_action_block21
  · exact allFin _ _ power_4_action_block22
  · exact allFin _ _ power_4_action_block23
  · exact allFin _ _ power_4_action_block24
  · exact allFin _ _ power_4_action_block25
  · exact allFin _ _ power_4_action_block26
  · exact allFin _ _ power_4_action_block27
  · exact allFin _ _ power_4_action_block28
  · exact allFin _ _ power_4_action_block29
  · exact allFin _ _ power_4_action_block30
  · exact allFin _ _ power_4_action_block31
  · exact allFin _ _ power_4_action_block32

theorem power_4 : pc 4 ^ relativeOrder 4 = ((powerWord 4).map pc).prod := by
  apply representation_injective
  simp only [map_pow, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext power_4_action

abbrev conj_4_5_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 * pcTable 5 * (pcTable 4)⁻¹) x = ((conjugateWord 4 5).map pcTable).prod x

private theorem conj_4_5_action_block0 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block1 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block2 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block3 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block4 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block5 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block6 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block7 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block8 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block9 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block10 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block11 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block12 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block13 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block14 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block15 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block16 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block17 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block18 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block19 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block20 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block21 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block22 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block23 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block24 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block25 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block26 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block27 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block28 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block29 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block30 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block31 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conj_4_5_action_block32 : checkFin 64 (fun j => decide (conj_4_5_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conj_4_5_action : ∀ x, conj_4_5_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conj_4_5_action_block0
  · exact allFin _ _ conj_4_5_action_block1
  · exact allFin _ _ conj_4_5_action_block2
  · exact allFin _ _ conj_4_5_action_block3
  · exact allFin _ _ conj_4_5_action_block4
  · exact allFin _ _ conj_4_5_action_block5
  · exact allFin _ _ conj_4_5_action_block6
  · exact allFin _ _ conj_4_5_action_block7
  · exact allFin _ _ conj_4_5_action_block8
  · exact allFin _ _ conj_4_5_action_block9
  · exact allFin _ _ conj_4_5_action_block10
  · exact allFin _ _ conj_4_5_action_block11
  · exact allFin _ _ conj_4_5_action_block12
  · exact allFin _ _ conj_4_5_action_block13
  · exact allFin _ _ conj_4_5_action_block14
  · exact allFin _ _ conj_4_5_action_block15
  · exact allFin _ _ conj_4_5_action_block16
  · exact allFin _ _ conj_4_5_action_block17
  · exact allFin _ _ conj_4_5_action_block18
  · exact allFin _ _ conj_4_5_action_block19
  · exact allFin _ _ conj_4_5_action_block20
  · exact allFin _ _ conj_4_5_action_block21
  · exact allFin _ _ conj_4_5_action_block22
  · exact allFin _ _ conj_4_5_action_block23
  · exact allFin _ _ conj_4_5_action_block24
  · exact allFin _ _ conj_4_5_action_block25
  · exact allFin _ _ conj_4_5_action_block26
  · exact allFin _ _ conj_4_5_action_block27
  · exact allFin _ _ conj_4_5_action_block28
  · exact allFin _ _ conj_4_5_action_block29
  · exact allFin _ _ conj_4_5_action_block30
  · exact allFin _ _ conj_4_5_action_block31
  · exact allFin _ _ conj_4_5_action_block32

theorem conj_4_5 : pc 4 * pc 5 * (pc 4)⁻¹ = ((conjugateWord 4 5).map pc).prod := by
  apply representation_injective
  simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext conj_4_5_action

abbrev conj_4_6_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 * pcTable 6 * (pcTable 4)⁻¹) x = ((conjugateWord 4 6).map pcTable).prod x

private theorem conj_4_6_action_block0 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block1 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block2 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block3 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block4 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block5 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block6 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block7 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block8 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block9 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block10 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block11 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block12 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block13 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block14 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block15 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block16 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block17 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block18 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block19 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block20 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block21 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block22 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block23 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block24 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block25 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block26 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block27 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block28 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block29 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block30 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block31 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conj_4_6_action_block32 : checkFin 64 (fun j => decide (conj_4_6_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conj_4_6_action : ∀ x, conj_4_6_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conj_4_6_action_block0
  · exact allFin _ _ conj_4_6_action_block1
  · exact allFin _ _ conj_4_6_action_block2
  · exact allFin _ _ conj_4_6_action_block3
  · exact allFin _ _ conj_4_6_action_block4
  · exact allFin _ _ conj_4_6_action_block5
  · exact allFin _ _ conj_4_6_action_block6
  · exact allFin _ _ conj_4_6_action_block7
  · exact allFin _ _ conj_4_6_action_block8
  · exact allFin _ _ conj_4_6_action_block9
  · exact allFin _ _ conj_4_6_action_block10
  · exact allFin _ _ conj_4_6_action_block11
  · exact allFin _ _ conj_4_6_action_block12
  · exact allFin _ _ conj_4_6_action_block13
  · exact allFin _ _ conj_4_6_action_block14
  · exact allFin _ _ conj_4_6_action_block15
  · exact allFin _ _ conj_4_6_action_block16
  · exact allFin _ _ conj_4_6_action_block17
  · exact allFin _ _ conj_4_6_action_block18
  · exact allFin _ _ conj_4_6_action_block19
  · exact allFin _ _ conj_4_6_action_block20
  · exact allFin _ _ conj_4_6_action_block21
  · exact allFin _ _ conj_4_6_action_block22
  · exact allFin _ _ conj_4_6_action_block23
  · exact allFin _ _ conj_4_6_action_block24
  · exact allFin _ _ conj_4_6_action_block25
  · exact allFin _ _ conj_4_6_action_block26
  · exact allFin _ _ conj_4_6_action_block27
  · exact allFin _ _ conj_4_6_action_block28
  · exact allFin _ _ conj_4_6_action_block29
  · exact allFin _ _ conj_4_6_action_block30
  · exact allFin _ _ conj_4_6_action_block31
  · exact allFin _ _ conj_4_6_action_block32

theorem conj_4_6 : pc 4 * pc 6 * (pc 4)⁻¹ = ((conjugateWord 4 6).map pc).prod := by
  apply representation_injective
  simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext conj_4_6_action

abbrev conj_4_7_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 * pcTable 7 * (pcTable 4)⁻¹) x = ((conjugateWord 4 7).map pcTable).prod x

private theorem conj_4_7_action_block0 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block1 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block2 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block3 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block4 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block5 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block6 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block7 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block8 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block9 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block10 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block11 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block12 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block13 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block14 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block15 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block16 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block17 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block18 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block19 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block20 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block21 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block22 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block23 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block24 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block25 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block26 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block27 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block28 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block29 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block30 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block31 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conj_4_7_action_block32 : checkFin 64 (fun j => decide (conj_4_7_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conj_4_7_action : ∀ x, conj_4_7_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conj_4_7_action_block0
  · exact allFin _ _ conj_4_7_action_block1
  · exact allFin _ _ conj_4_7_action_block2
  · exact allFin _ _ conj_4_7_action_block3
  · exact allFin _ _ conj_4_7_action_block4
  · exact allFin _ _ conj_4_7_action_block5
  · exact allFin _ _ conj_4_7_action_block6
  · exact allFin _ _ conj_4_7_action_block7
  · exact allFin _ _ conj_4_7_action_block8
  · exact allFin _ _ conj_4_7_action_block9
  · exact allFin _ _ conj_4_7_action_block10
  · exact allFin _ _ conj_4_7_action_block11
  · exact allFin _ _ conj_4_7_action_block12
  · exact allFin _ _ conj_4_7_action_block13
  · exact allFin _ _ conj_4_7_action_block14
  · exact allFin _ _ conj_4_7_action_block15
  · exact allFin _ _ conj_4_7_action_block16
  · exact allFin _ _ conj_4_7_action_block17
  · exact allFin _ _ conj_4_7_action_block18
  · exact allFin _ _ conj_4_7_action_block19
  · exact allFin _ _ conj_4_7_action_block20
  · exact allFin _ _ conj_4_7_action_block21
  · exact allFin _ _ conj_4_7_action_block22
  · exact allFin _ _ conj_4_7_action_block23
  · exact allFin _ _ conj_4_7_action_block24
  · exact allFin _ _ conj_4_7_action_block25
  · exact allFin _ _ conj_4_7_action_block26
  · exact allFin _ _ conj_4_7_action_block27
  · exact allFin _ _ conj_4_7_action_block28
  · exact allFin _ _ conj_4_7_action_block29
  · exact allFin _ _ conj_4_7_action_block30
  · exact allFin _ _ conj_4_7_action_block31
  · exact allFin _ _ conj_4_7_action_block32

theorem conj_4_7 : pc 4 * pc 7 * (pc 4)⁻¹ = ((conjugateWord 4 7).map pc).prod := by
  apply representation_injective
  simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext conj_4_7_action

abbrev conj_4_8_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 * pcTable 8 * (pcTable 4)⁻¹) x = ((conjugateWord 4 8).map pcTable).prod x

private theorem conj_4_8_action_block0 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block1 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block2 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block3 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block4 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block5 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block6 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block7 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block8 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block9 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block10 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block11 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block12 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block13 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block14 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block15 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block16 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block17 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block18 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block19 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block20 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block21 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block22 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block23 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block24 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block25 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block26 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block27 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block28 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block29 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block30 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block31 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conj_4_8_action_block32 : checkFin 64 (fun j => decide (conj_4_8_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conj_4_8_action : ∀ x, conj_4_8_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conj_4_8_action_block0
  · exact allFin _ _ conj_4_8_action_block1
  · exact allFin _ _ conj_4_8_action_block2
  · exact allFin _ _ conj_4_8_action_block3
  · exact allFin _ _ conj_4_8_action_block4
  · exact allFin _ _ conj_4_8_action_block5
  · exact allFin _ _ conj_4_8_action_block6
  · exact allFin _ _ conj_4_8_action_block7
  · exact allFin _ _ conj_4_8_action_block8
  · exact allFin _ _ conj_4_8_action_block9
  · exact allFin _ _ conj_4_8_action_block10
  · exact allFin _ _ conj_4_8_action_block11
  · exact allFin _ _ conj_4_8_action_block12
  · exact allFin _ _ conj_4_8_action_block13
  · exact allFin _ _ conj_4_8_action_block14
  · exact allFin _ _ conj_4_8_action_block15
  · exact allFin _ _ conj_4_8_action_block16
  · exact allFin _ _ conj_4_8_action_block17
  · exact allFin _ _ conj_4_8_action_block18
  · exact allFin _ _ conj_4_8_action_block19
  · exact allFin _ _ conj_4_8_action_block20
  · exact allFin _ _ conj_4_8_action_block21
  · exact allFin _ _ conj_4_8_action_block22
  · exact allFin _ _ conj_4_8_action_block23
  · exact allFin _ _ conj_4_8_action_block24
  · exact allFin _ _ conj_4_8_action_block25
  · exact allFin _ _ conj_4_8_action_block26
  · exact allFin _ _ conj_4_8_action_block27
  · exact allFin _ _ conj_4_8_action_block28
  · exact allFin _ _ conj_4_8_action_block29
  · exact allFin _ _ conj_4_8_action_block30
  · exact allFin _ _ conj_4_8_action_block31
  · exact allFin _ _ conj_4_8_action_block32

theorem conj_4_8 : pc 4 * pc 8 * (pc 4)⁻¹ = ((conjugateWord 4 8).map pc).prod := by
  apply representation_injective
  simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext conj_4_8_action

abbrev conj_4_9_actionPredicate (x : Fin 2058) : Prop := (pcTable 4 * pcTable 9 * (pcTable 4)⁻¹) x = ((conjugateWord 4 9).map pcTable).prod x

private theorem conj_4_9_action_block0 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block1 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block2 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block3 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block4 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block5 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block6 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block7 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block8 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block9 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block10 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block11 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block12 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block13 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block14 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block15 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block16 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block17 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block18 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block19 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block20 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block21 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block22 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block23 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block24 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block25 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block26 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block27 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block28 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block29 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block30 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block31 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conj_4_9_action_block32 : checkFin 64 (fun j => decide (conj_4_9_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conj_4_9_action : ∀ x, conj_4_9_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conj_4_9_action_block0
  · exact allFin _ _ conj_4_9_action_block1
  · exact allFin _ _ conj_4_9_action_block2
  · exact allFin _ _ conj_4_9_action_block3
  · exact allFin _ _ conj_4_9_action_block4
  · exact allFin _ _ conj_4_9_action_block5
  · exact allFin _ _ conj_4_9_action_block6
  · exact allFin _ _ conj_4_9_action_block7
  · exact allFin _ _ conj_4_9_action_block8
  · exact allFin _ _ conj_4_9_action_block9
  · exact allFin _ _ conj_4_9_action_block10
  · exact allFin _ _ conj_4_9_action_block11
  · exact allFin _ _ conj_4_9_action_block12
  · exact allFin _ _ conj_4_9_action_block13
  · exact allFin _ _ conj_4_9_action_block14
  · exact allFin _ _ conj_4_9_action_block15
  · exact allFin _ _ conj_4_9_action_block16
  · exact allFin _ _ conj_4_9_action_block17
  · exact allFin _ _ conj_4_9_action_block18
  · exact allFin _ _ conj_4_9_action_block19
  · exact allFin _ _ conj_4_9_action_block20
  · exact allFin _ _ conj_4_9_action_block21
  · exact allFin _ _ conj_4_9_action_block22
  · exact allFin _ _ conj_4_9_action_block23
  · exact allFin _ _ conj_4_9_action_block24
  · exact allFin _ _ conj_4_9_action_block25
  · exact allFin _ _ conj_4_9_action_block26
  · exact allFin _ _ conj_4_9_action_block27
  · exact allFin _ _ conj_4_9_action_block28
  · exact allFin _ _ conj_4_9_action_block29
  · exact allFin _ _ conj_4_9_action_block30
  · exact allFin _ _ conj_4_9_action_block31
  · exact allFin _ _ conj_4_9_action_block32

theorem conj_4_9 : pc 4 * pc 9 * (pc 4)⁻¹ = ((conjugateWord 4 9).map pc).prod := by
  apply representation_injective
  simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq]
  exact Equiv.ext conj_4_9_action


end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
