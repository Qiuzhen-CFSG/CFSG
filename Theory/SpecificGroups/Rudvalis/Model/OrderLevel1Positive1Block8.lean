module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches312To316
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches322To326
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches332To336
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches347To350
import Mathlib.Tactic.FinCases

/-!
# Ninth block of certificates for the second positive Rudvalis level-1 generator

This assembles batches 312–350, covering representatives 1560–1754. Each batch
first uses proved free cancellation and otherwise checks equality on all 4060
points in Lean's kernel. The eight bounded range certificates cover all 39
values of `blockBatch 8`, establishing `block 8` without further computation.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
Checker correctness is proved in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
set_option Elab.async false

/-- The 195 transitions in batches 312 through 350. -/
public theorem block8 : block 8 := by
  intro b
  fin_cases b
  · exact Block8.segment312 0
  · exact Block8.segment312 1
  · exact Block8.segment312 2
  · exact Block8.segment312 3
  · exact Block8.segment312 4
  · exact Block8.segment317 0
  · exact Block8.segment317 1
  · exact Block8.segment317 2
  · exact Block8.segment317 3
  · exact Block8.segment317 4
  · exact Block8.segment322 0
  · exact Block8.segment322 1
  · exact Block8.segment322 2
  · exact Block8.segment322 3
  · exact Block8.segment322 4
  · exact Block8.segment327 0
  · exact Block8.segment327 1
  · exact Block8.segment327 2
  · exact Block8.segment327 3
  · exact Block8.segment327 4
  · exact Block8.segment332 0
  · exact Block8.segment332 1
  · exact Block8.segment332 2
  · exact Block8.segment332 3
  · exact Block8.segment332 4
  · exact Block8.segment337 0
  · exact Block8.segment337 1
  · exact Block8.segment337 2
  · exact Block8.segment337 3
  · exact Block8.segment337 4
  · exact Block8.segment342 0
  · exact Block8.segment342 1
  · exact Block8.segment342 2
  · exact Block8.segment342 3
  · exact Block8.segment342 4
  · exact Block8.segment347 0
  · exact Block8.segment347 1
  · exact Block8.segment347 2
  · exact Block8.segment347 3

end Rudvalis.OrderCertificate.OrderLevel1Positive1
