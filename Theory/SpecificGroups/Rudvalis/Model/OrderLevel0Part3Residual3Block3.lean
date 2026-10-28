module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point255
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point256
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point257
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point258
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point259
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point260
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point261
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point262
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point263
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point264
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point265
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point266
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point267
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point268
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point269
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block3.Point270
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual interval 255–270

Assemble the separately kernel-checked permutation identities in this interval.
Source: `OrderLevel0Part3ResidualReduction.target` and `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks

public theorem block3 : subbatch 3 := by
  intro s hs
  fin_cases s
  · exact point255
  · exact point256
  · exact point257
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
  · exact (Nat.lt_irrefl 271 hs).elim

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
