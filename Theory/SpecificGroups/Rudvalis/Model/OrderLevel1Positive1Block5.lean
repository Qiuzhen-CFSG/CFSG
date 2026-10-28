module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches195To199
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches205To209
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches215To219
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches230To233
import Mathlib.Tactic.FinCases

/-!
# Sixth block of certificates for the second positive Rudvalis level-1 generator

This assembles batches 195–233, covering representatives 975–1169. Each batch
first checks free cancellation and otherwise checks equality on all 4060 points
in Lean's kernel. Sequential supporting modules preserve completed checks as
reusable build artifacts. The 39 certificates assemble into `block 5`.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
set_option Elab.async false

/-- The 195 transitions in batches 195 through 233. -/
public theorem block5 : block 5 := by
  intro b
  fin_cases b
  · exact Block5.segment195 0
  · exact Block5.segment195 1
  · exact Block5.segment195 2
  · exact Block5.segment195 3
  · exact Block5.segment195 4
  · exact Block5.segment200 0
  · exact Block5.segment200 1
  · exact Block5.segment200 2
  · exact Block5.segment200 3
  · exact Block5.segment200 4
  · exact Block5.segment205 0
  · exact Block5.segment205 1
  · exact Block5.segment205 2
  · exact Block5.segment205 3
  · exact Block5.segment205 4
  · exact Block5.segment210 0
  · exact Block5.segment210 1
  · exact Block5.segment210 2
  · exact Block5.segment210 3
  · exact Block5.segment210 4
  · exact Block5.segment215 0
  · exact Block5.segment215 1
  · exact Block5.segment215 2
  · exact Block5.segment215 3
  · exact Block5.segment215 4
  · exact Block5.segment220 0
  · exact Block5.segment220 1
  · exact Block5.segment220 2
  · exact Block5.segment220 3
  · exact Block5.segment220 4
  · exact Block5.segment225 0
  · exact Block5.segment225 1
  · exact Block5.segment225 2
  · exact Block5.segment225 3
  · exact Block5.segment225 4
  · exact Block5.segment230 0
  · exact Block5.segment230 1
  · exact Block5.segment230 2
  · exact Block5.segment230 3

end Rudvalis.OrderCertificate.OrderLevel1Positive1
