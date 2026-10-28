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
private theorem checked60_0 : partialStep 60 0 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_1 : partialStep 60 1 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_2 : partialStep 60 2 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_3 : partialStep 60 3 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_4 : partialStep 60 4 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_5 : partialStep 60 5 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_6 : partialStep 60 6 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_7 : partialStep 60 7 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_8 : partialStep 60 8 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_9 : partialStep 60 9 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_10 : partialStep 60 10 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked60_11 : partialStep 60 11 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

public theorem checked60 : stepBatch 60 := by
  apply ofPartialSteps
  intro c
  fin_cases c
  · exact checked60_0
  · exact checked60_1
  · exact checked60_2
  · exact checked60_3
  · exact checked60_4
  · exact checked60_5
  · exact checked60_6
  · exact checked60_7
  · exact checked60_8
  · exact checked60_9
  · exact checked60_10
  · exact checked60_11


end Sporadic.Janko3.OrderCertificate.Level1
