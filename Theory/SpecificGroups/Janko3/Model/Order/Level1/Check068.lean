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
private theorem checked68_0 : partialStep 68 0 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_1 : partialStep 68 1 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_2 : partialStep 68 2 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_3 : partialStep 68 3 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_4 : partialStep 68 4 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_5 : partialStep 68 5 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_6 : partialStep 68 6 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_7 : partialStep 68 7 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_8 : partialStep 68 8 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_9 : partialStep 68 9 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_10 : partialStep 68 10 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked68_11 : partialStep 68 11 := by
  apply ofPartialCheck
  apply allFin₂
  decide +kernel

public theorem checked68 : stepBatch 68 := by
  apply ofPartialSteps
  intro c
  fin_cases c
  · exact checked68_0
  · exact checked68_1
  · exact checked68_2
  · exact checked68_3
  · exact checked68_4
  · exact checked68_5
  · exact checked68_6
  · exact checked68_7
  · exact checked68_8
  · exact checked68_9
  · exact checked68_10
  · exact checked68_11


end Sporadic.Janko3.OrderCertificate.Level1
