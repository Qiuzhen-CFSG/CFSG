module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair11Odd.Collect0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair11Odd.Collect1
import Mathlib.Tactic.FinCases

/-!
# The original generators lie in the cyclic series

The literal ATLAS degree-2058 action certifies every identity by kernel
reduction in bounded blocks. No numerical GAP output is a proof premise.
Sources: HeG1-p2058B0, max3/max4 programs, and LocalActions/source/Explore.g.
Reproduction: Factors/source/generate.py; proposed series: ../source/pcdata.json.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair11Odd
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

abbrev input_0_actionPredicate (x : Fin 2058) : Prop := inputTable 0 x = ((inputWord 0).map pcTable).prod x

private theorem input_0_action_block0 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem input_0_action_block1 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem input_0_action_block2 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem input_0_action_block3 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem input_0_action_block4 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem input_0_action_block5 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem input_0_action_block6 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem input_0_action_block7 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem input_0_action_block8 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem input_0_action_block9 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem input_0_action_block10 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem input_0_action_block11 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem input_0_action_block12 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem input_0_action_block13 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem input_0_action_block14 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem input_0_action_block15 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem input_0_action_block16 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem input_0_action_block17 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem input_0_action_block18 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem input_0_action_block19 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem input_0_action_block20 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem input_0_action_block21 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem input_0_action_block22 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem input_0_action_block23 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem input_0_action_block24 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem input_0_action_block25 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem input_0_action_block26 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem input_0_action_block27 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem input_0_action_block28 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem input_0_action_block29 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem input_0_action_block30 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem input_0_action_block31 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem input_0_action_block32 : checkFin 64 (fun j => decide (input_0_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem input_0_action : ∀ x, input_0_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ input_0_action_block0
  · exact allFin _ _ input_0_action_block1
  · exact allFin _ _ input_0_action_block2
  · exact allFin _ _ input_0_action_block3
  · exact allFin _ _ input_0_action_block4
  · exact allFin _ _ input_0_action_block5
  · exact allFin _ _ input_0_action_block6
  · exact allFin _ _ input_0_action_block7
  · exact allFin _ _ input_0_action_block8
  · exact allFin _ _ input_0_action_block9
  · exact allFin _ _ input_0_action_block10
  · exact allFin _ _ input_0_action_block11
  · exact allFin _ _ input_0_action_block12
  · exact allFin _ _ input_0_action_block13
  · exact allFin _ _ input_0_action_block14
  · exact allFin _ _ input_0_action_block15
  · exact allFin _ _ input_0_action_block16
  · exact allFin _ _ input_0_action_block17
  · exact allFin _ _ input_0_action_block18
  · exact allFin _ _ input_0_action_block19
  · exact allFin _ _ input_0_action_block20
  · exact allFin _ _ input_0_action_block21
  · exact allFin _ _ input_0_action_block22
  · exact allFin _ _ input_0_action_block23
  · exact allFin _ _ input_0_action_block24
  · exact allFin _ _ input_0_action_block25
  · exact allFin _ _ input_0_action_block26
  · exact allFin _ _ input_0_action_block27
  · exact allFin _ _ input_0_action_block28
  · exact allFin _ _ input_0_action_block29
  · exact allFin _ _ input_0_action_block30
  · exact allFin _ _ input_0_action_block31
  · exact allFin _ _ input_0_action_block32

theorem input_0 : input 0 = ((inputWord 0).map pc).prod := by
  apply representation_injective
  simp only [map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq, ← inputTable_eq]
  exact Equiv.ext input_0_action

abbrev input_1_actionPredicate (x : Fin 2058) : Prop := inputTable 1 x = ((inputWord 1).map pcTable).prod x

private theorem input_1_action_block0 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem input_1_action_block1 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem input_1_action_block2 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem input_1_action_block3 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem input_1_action_block4 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem input_1_action_block5 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem input_1_action_block6 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem input_1_action_block7 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem input_1_action_block8 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem input_1_action_block9 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem input_1_action_block10 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem input_1_action_block11 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem input_1_action_block12 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem input_1_action_block13 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem input_1_action_block14 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem input_1_action_block15 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem input_1_action_block16 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem input_1_action_block17 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem input_1_action_block18 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem input_1_action_block19 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem input_1_action_block20 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem input_1_action_block21 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem input_1_action_block22 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem input_1_action_block23 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem input_1_action_block24 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem input_1_action_block25 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem input_1_action_block26 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem input_1_action_block27 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem input_1_action_block28 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem input_1_action_block29 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem input_1_action_block30 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem input_1_action_block31 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem input_1_action_block32 : checkFin 64 (fun j => decide (input_1_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem input_1_action : ∀ x, input_1_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ input_1_action_block0
  · exact allFin _ _ input_1_action_block1
  · exact allFin _ _ input_1_action_block2
  · exact allFin _ _ input_1_action_block3
  · exact allFin _ _ input_1_action_block4
  · exact allFin _ _ input_1_action_block5
  · exact allFin _ _ input_1_action_block6
  · exact allFin _ _ input_1_action_block7
  · exact allFin _ _ input_1_action_block8
  · exact allFin _ _ input_1_action_block9
  · exact allFin _ _ input_1_action_block10
  · exact allFin _ _ input_1_action_block11
  · exact allFin _ _ input_1_action_block12
  · exact allFin _ _ input_1_action_block13
  · exact allFin _ _ input_1_action_block14
  · exact allFin _ _ input_1_action_block15
  · exact allFin _ _ input_1_action_block16
  · exact allFin _ _ input_1_action_block17
  · exact allFin _ _ input_1_action_block18
  · exact allFin _ _ input_1_action_block19
  · exact allFin _ _ input_1_action_block20
  · exact allFin _ _ input_1_action_block21
  · exact allFin _ _ input_1_action_block22
  · exact allFin _ _ input_1_action_block23
  · exact allFin _ _ input_1_action_block24
  · exact allFin _ _ input_1_action_block25
  · exact allFin _ _ input_1_action_block26
  · exact allFin _ _ input_1_action_block27
  · exact allFin _ _ input_1_action_block28
  · exact allFin _ _ input_1_action_block29
  · exact allFin _ _ input_1_action_block30
  · exact allFin _ _ input_1_action_block31
  · exact allFin _ _ input_1_action_block32

theorem input_1 : input 1 = ((inputWord 1).map pc).prod := by
  apply representation_injective
  simp only [map_list_prod, List.map_map, Function.comp_def, ← pcTable_eq, ← inputTable_eq]
  exact Equiv.ext input_1_action


end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair11Odd
