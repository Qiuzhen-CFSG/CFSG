module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point46
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point47
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point48
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point49
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point50
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point51
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point52
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point53
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point54
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point55
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point56
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point57
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point58
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point59
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point60
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point61
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point62
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point63
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point64
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point65
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point66
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point67
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block2.Point68
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 46 through 68

Assemble the 23 pointwise transition certificates for this interval.
Each certificate checks the exact words prescribed by `Part5Residual.target`
on all 4060 points, using the kernel-certified packed evaluator. Source:
`OrderLevel0Data` and `OrderCertificate/GenerateLevel0Part5Residual0.py`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks

public theorem block2 : block 2 := by
  intro s
  fin_cases s
  · exact point46
  · exact point47
  · exact point48
  · exact point49
  · exact point50
  · exact point51
  · exact point52
  · exact point53
  · exact point54
  · exact point55
  · exact point56
  · exact point57
  · exact point58
  · exact point59
  · exact point60
  · exact point61
  · exact point62
  · exact point63
  · exact point64
  · exact point65
  · exact point66
  · exact point67
  · exact point68

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks
