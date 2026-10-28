module

public import Theory.SpecificGroups.Janko3.Model.Order.Level1.Batches
import Mathlib.Tactic.FinCases

/-!
# Kernel certification of the second J3 Schreier step

The two forward generators are checked on all 510 representatives and all
6156 letters. Word reduction handles the algebraic cases. Each remaining
check covers at most five representatives and 513 letters, and declarations
are elaborated sequentially to bound memory. Inverse transitions are recovered
by the separately certified terminal word calculation in `Reduction`.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level1
set_option maxRecDepth 40000
set_option Elab.async false

set_option maxHeartbeats 4000000 in
private theorem checked14_0 : partialStep 14 0 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_1 : partialStep 14 1 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_2 : partialStep 14 2 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_3 : partialStep 14 3 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_4 : partialStep 14 4 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_5 : partialStep 14 5 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_6 : partialStep 14 6 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_7 : partialStep 14 7 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_8 : partialStep 14 8 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_9 : partialStep 14 9 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_10 : partialStep 14 10 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked14_11 : partialStep 14 11 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

public theorem checked14 : stepBatch 14 := by
  apply ofPartialSteps
  intro c
  fin_cases c
  · exact checked14_0
  · exact checked14_1
  · exact checked14_2
  · exact checked14_3
  · exact checked14_4
  · exact checked14_5
  · exact checked14_6
  · exact checked14_7
  · exact checked14_8
  · exact checked14_9
  · exact checked14_10
  · exact checked14_11


end Sporadic.Janko3.OrderCertificate.Level1
