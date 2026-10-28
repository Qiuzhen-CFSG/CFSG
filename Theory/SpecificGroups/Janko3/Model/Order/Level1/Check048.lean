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
private theorem checked48_0 : partialStep 48 0 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_1 : partialStep 48 1 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_2 : partialStep 48 2 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_3 : partialStep 48 3 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_4 : partialStep 48 4 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_5 : partialStep 48 5 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_6 : partialStep 48 6 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_7 : partialStep 48 7 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_8 : partialStep 48 8 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_9 : partialStep 48 9 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_10 : partialStep 48 10 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked48_11 : partialStep 48 11 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

public theorem checked48 : stepBatch 48 := by
  apply ofPartialSteps
  intro c
  fin_cases c
  · exact checked48_0
  · exact checked48_1
  · exact checked48_2
  · exact checked48_3
  · exact checked48_4
  · exact checked48_5
  · exact checked48_6
  · exact checked48_7
  · exact checked48_8
  · exact checked48_9
  · exact checked48_10
  · exact checked48_11


end Sporadic.Janko3.OrderCertificate.Level1
