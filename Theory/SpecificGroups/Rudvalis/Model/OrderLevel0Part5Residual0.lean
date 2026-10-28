module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2

import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 0 through 68

Three checked intervals recover the first residual batch via division with
remainder. Source: `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual

public theorem residuals0 : residualBatch 0 := by
  apply Residual0Checks.residuals0_of_blocks
  intro b
  fin_cases b
  · exact Residual0Checks.block0
  · exact Residual0Checks.block1
  · exact Residual0Checks.block2

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual
