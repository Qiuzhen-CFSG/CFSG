module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Block3
import Mathlib.Tactic.FinCases

/-!
# Last group of Rudvalis part-3 residual transitions

The four independently checked intervals certify the fixed transitions at
indices 204 through 270. Source: `OrderLevel0Part3ResidualReduction.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual

public theorem residuals3 : residualBatch 3 := by
  apply Residual3Checks.ofSubbatches
  intro b
  fin_cases b
  · exact Residual3Checks.block0
  · exact Residual3Checks.block1
  · exact Residual3Checks.block2
  · exact Residual3Checks.block3

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual
