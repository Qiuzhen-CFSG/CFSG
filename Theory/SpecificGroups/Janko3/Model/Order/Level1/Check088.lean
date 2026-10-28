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
private theorem checked88_0 : partialStep 88 0 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_1 : partialStep 88 1 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_2 : partialStep 88 2 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_3 : partialStep 88 3 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_4 : partialStep 88 4 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_5 : partialStep 88 5 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_6 : partialStep 88 6 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_7 : partialStep 88 7 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_8 : partialStep 88 8 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_9 : partialStep 88 9 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_10 : partialStep 88 10 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked88_11 : partialStep 88 11 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

public theorem checked88 : stepBatch 88 := by
  apply ofPartialSteps
  intro c
  fin_cases c
  · exact checked88_0
  · exact checked88_1
  · exact checked88_2
  · exact checked88_3
  · exact checked88_4
  · exact checked88_5
  · exact checked88_6
  · exact checked88_7
  · exact checked88_8
  · exact checked88_9
  · exact checked88_10
  · exact checked88_11


end Sporadic.Janko3.OrderCertificate.Level1
