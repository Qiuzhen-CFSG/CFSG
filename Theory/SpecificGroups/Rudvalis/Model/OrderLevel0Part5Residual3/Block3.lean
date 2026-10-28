module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point258
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point259
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point260
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point261
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point262
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point263
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point264
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point265
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point266
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point267
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point268
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point269
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point270
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point271
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point272
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point273
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block3.Point274
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 258 through 274

The seventeen independently checked transition certificates give block 3 of
the final residual batch. Each certificate uses precisely the transition
specified by `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks

public theorem checked3 : block 3 := by
  intro s
  fin_cases s
  · exact point258
  · exact point259
  · exact point260
  · exact point261
  · exact point262
  · exact point263
  · exact point264
  · exact point265
  · exact point266
  · exact point267
  · exact point268
  · exact point269
  · exact point270
  · exact point271
  · exact point272
  · exact point273
  · exact point274

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
