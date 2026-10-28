module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockBPart5
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 100–183

The six kernel-checked subcertificates cover the 420 representatives in this
range. Finite case analysis assembles their exact transition identities.
Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
set_option Elab.async false

/-- Batches 100 through 183 satisfy the positive-generator-0 transition identity. -/
public theorem blockB (b : Fin 84) :
    Level1Reduction.stepBatch 0 ⟨100 + b.val, by omega⟩ := by
  fin_cases b
  · exact BlockB.part0 0
  · exact BlockB.part0 1
  · exact BlockB.part0 2
  · exact BlockB.part0 3
  · exact BlockB.part0 4
  · exact BlockB.part0 5
  · exact BlockB.part0 6
  · exact BlockB.part0 7
  · exact BlockB.part0 8
  · exact BlockB.part0 9
  · exact BlockB.part0 10
  · exact BlockB.part0 11
  · exact BlockB.part0 12
  · exact BlockB.part0 13
  · exact BlockB.part1 0
  · exact BlockB.part1 1
  · exact BlockB.part1 2
  · exact BlockB.part1 3
  · exact BlockB.part1 4
  · exact BlockB.part1 5
  · exact BlockB.part1 6
  · exact BlockB.part1 7
  · exact BlockB.part1 8
  · exact BlockB.part1 9
  · exact BlockB.part1 10
  · exact BlockB.part1 11
  · exact BlockB.part1 12
  · exact BlockB.part1 13
  · exact BlockB.part2 0
  · exact BlockB.part2 1
  · exact BlockB.part2 2
  · exact BlockB.part2 3
  · exact BlockB.part2 4
  · exact BlockB.part2 5
  · exact BlockB.part2 6
  · exact BlockB.part2 7
  · exact BlockB.part2 8
  · exact BlockB.part2 9
  · exact BlockB.part2 10
  · exact BlockB.part2 11
  · exact BlockB.part2 12
  · exact BlockB.part2 13
  · exact BlockB.part3 0
  · exact BlockB.part3 1
  · exact BlockB.part3 2
  · exact BlockB.part3 3
  · exact BlockB.part3 4
  · exact BlockB.part3 5
  · exact BlockB.part3 6
  · exact BlockB.part3 7
  · exact BlockB.part3 8
  · exact BlockB.part3 9
  · exact BlockB.part3 10
  · exact BlockB.part3 11
  · exact BlockB.part3 12
  · exact BlockB.part3 13
  · exact BlockB.part4 0
  · exact BlockB.part4 1
  · exact BlockB.part4 2
  · exact BlockB.part4 3
  · exact BlockB.part4 4
  · exact BlockB.part4 5
  · exact BlockB.part4 6
  · exact BlockB.part4 7
  · exact BlockB.part4 8
  · exact BlockB.part4 9
  · exact BlockB.part4 10
  · exact BlockB.part4 11
  · exact BlockB.part4 12
  · exact BlockB.part4 13
  · exact BlockB.part5 0
  · exact BlockB.part5 1
  · exact BlockB.part5 2
  · exact BlockB.part5 3
  · exact BlockB.part5 4
  · exact BlockB.part5 5
  · exact BlockB.part5 6
  · exact BlockB.part5 7
  · exact BlockB.part5 8
  · exact BlockB.part5 9
  · exact BlockB.part5 10
  · exact BlockB.part5 11
  · exact BlockB.part5 12
  · exact BlockB.part5 13

end Rudvalis.OrderCertificate.OrderLevel1Positive0
