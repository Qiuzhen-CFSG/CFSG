module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block3
import Mathlib.Tactic.FinCases

/-!
# Third residual batch of the Rudvalis part-3 certificate

The four independently checked blocks cover the fixed residual indices
136 through 203. Source: `Part3Residual.target` in
`OrderLevel0Part3ResidualReduction` and the witnesses in `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual

/-- The 68 prescribed transitions in residual group 2. -/
public theorem residuals2 : residualBatch 2 := by
  apply Residual2.assemble
  intro b
  fin_cases b
  · exact Residual2.block0
  · exact Residual2.block1
  · exact Residual2.block2
  · exact Residual2.block3

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual
