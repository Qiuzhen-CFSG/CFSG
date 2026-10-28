module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point221
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point222
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point223
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point224
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point225
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point226
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point227
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point228
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point229
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point230
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point231
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point232
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point233
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point234
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point235
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point236
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block1.Point237
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual interval 221–237

Assemble the separately kernel-checked permutation identities in this interval.
Source: `OrderLevel0Part3ResidualReduction.target` and `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks

public theorem block1 : subbatch 1 := by
  intro s hs
  fin_cases s
  · exact point221
  · exact point222
  · exact point223
  · exact point224
  · exact point225
  · exact point226
  · exact point227
  · exact point228
  · exact point229
  · exact point230
  · exact point231
  · exact point232
  · exact point233
  · exact point234
  · exact point235
  · exact point236
  · exact point237

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
