module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point224
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point225
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point226
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point227
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point228
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point229
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point230
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point231
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point232
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point233
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point234
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point235
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point236
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point237
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point238
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point239
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block1.Point240
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 224 through 240

Assemble the seventeen pointwise transition certificates into block 1 of the
last residual batch. Each certificate uses the exact transition specified in
`Part5Residual.target`; finite case analysis identifies its residual index.

Source: `OrderLevel0Part5ResidualReduction` and `OrderCertificate/GenerateChain.g`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks

public theorem checked1 : block 1 := by
  intro s
  fin_cases s
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
  · exact point238
  · exact point239
  · exact point240

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
