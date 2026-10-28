module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point23
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point24
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point25
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point26
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point27
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point28
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point29
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point30
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point31
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point32
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point33
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point34
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point35
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point36
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point37
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point38
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point39
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point40
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point41
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point42
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point43
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point44
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Block1.Point45
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0.Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 23 through 45

Assemble the 23 pointwise transition certificates for this interval.
Each certificate checks the exact words prescribed by `Part5Residual.target`
on all 4060 points, using the kernel-certified packed evaluator. Source:
`OrderLevel0Data` and `OrderCertificate/GenerateLevel0Part5Residual0.py`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks

public theorem block1 : block 1 := by
  intro s
  fin_cases s
  · exact point23
  · exact point24
  · exact point25
  · exact point26
  · exact point27
  · exact point28
  · exact point29
  · exact point30
  · exact point31
  · exact point32
  · exact point33
  · exact point34
  · exact point35
  · exact point36
  · exact point37
  · exact point38
  · exact point39
  · exact point40
  · exact point41
  · exact point42
  · exact point43
  · exact point44
  · exact point45

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks
