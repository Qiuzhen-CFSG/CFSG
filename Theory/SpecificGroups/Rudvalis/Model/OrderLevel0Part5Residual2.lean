module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block2
import Mathlib.Tactic.FinCases

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual

public theorem residuals2 : residualBatch 2 := by
  apply Residual2.assemble
  intro b
  fin_cases b
  · exact Residual2.checked0
  · exact Residual2.checked1
  · exact Residual2.checked2

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual
