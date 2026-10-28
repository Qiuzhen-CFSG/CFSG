module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3
import Mathlib.Tactic.FinCases

/-!
# Final Rudvalis part-5 residual batch

The four certified blocks cover residual indices 207 through 274. The coverage
theorem assembles their exact transition checks into batch 3, whose bound
excludes local index 68.

Source: `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`, with
transition witnesses from `OrderLevel0Data` and `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual

/-- The last batch of residual transition identities for level-0 part 5. -/
public theorem residuals3 : residualBatch 3 := by
  apply Residual3Checks.ofBlocks
  intro b
  fin_cases b
  · exact Residual3Checks.checked0
  · exact Residual3Checks.checked1
  · exact Residual3Checks.checked2
  · exact Residual3Checks.checked3

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual
