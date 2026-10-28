module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Checks
import Mathlib.Tactic.FinCases

/-!
# First exceptional A transition

This certifies representative 251, the first transition not proved by the
A² = B³ = 1 normalization. Eighteen bounded point certificates prove the full
6156-letter identity without native computation or a stabilizer assumption.
Source: ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
set_option maxRecDepth 40000
set_option Elab.async false

private theorem checked0 : aPointBlock 251 0 := by
  apply allFin₂
  decide +kernel

private theorem checked1 : aPointBlock 251 1 := by
  apply allFin₂
  decide +kernel

private theorem checked2 : aPointBlock 251 2 := by
  apply allFin₂
  decide +kernel

private theorem checked3 : aPointBlock 251 3 := by
  apply allFin₂
  decide +kernel

private theorem checked4 : aPointBlock 251 4 := by
  apply allFin₂
  decide +kernel

private theorem checked5 : aPointBlock 251 5 := by
  apply allFin₂
  decide +kernel

private theorem checked6 : aPointBlock 251 6 := by
  apply allFin₂
  decide +kernel

private theorem checked7 : aPointBlock 251 7 := by
  apply allFin₂
  decide +kernel

private theorem checked8 : aPointBlock 251 8 := by
  apply allFin₂
  decide +kernel

private theorem checked9 : aPointBlock 251 9 := by
  apply allFin₂
  decide +kernel

private theorem checked10 : aPointBlock 251 10 := by
  apply allFin₂
  decide +kernel

private theorem checked11 : aPointBlock 251 11 := by
  apply allFin₂
  decide +kernel

private theorem checked12 : aPointBlock 251 12 := by
  apply allFin₂
  decide +kernel

private theorem checked13 : aPointBlock 251 13 := by
  apply allFin₂
  decide +kernel

private theorem checked14 : aPointBlock 251 14 := by
  apply allFin₂
  decide +kernel

private theorem checked15 : aPointBlock 251 15 := by
  apply allFin₂
  decide +kernel

private theorem checked16 : aPointBlock 251 16 := by
  apply allFin₂
  decide +kernel

private theorem checked17 : aPointBlock 251 17 := by
  apply allFin₂
  decide +kernel

public theorem forwardA251 : forwardAStep 251 := by
  apply forwardAStep_of_pointBlocks
  intro b
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17

end Sporadic.Janko3.OrderCertificate.Level0
