module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point241
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point242
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point243
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point244
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point245
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point246
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point247
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point248
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point249
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point250
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point251
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point252
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point253
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point254
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point255
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point256
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3.Block2Checks.Point257
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residuals 241 through 257

Assemble the seventeen independently kernel-checked transition certificates.
The prescribed transitions are those of `Part5Residual.target`; each certificate
uses `Part6Nat.ofSlices` to cover all 4060 points. Source: `OrderLevel0Data`
and the ATLAS witnesses documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks

public theorem checked2 : block 2 := by
  intro s
  fin_cases s
  · exact Block2Checks.point241
  · exact Block2Checks.point242
  · exact Block2Checks.point243
  · exact Block2Checks.point244
  · exact Block2Checks.point245
  · exact Block2Checks.point246
  · exact Block2Checks.point247
  · exact Block2Checks.point248
  · exact Block2Checks.point249
  · exact Block2Checks.point250
  · exact Block2Checks.point251
  · exact Block2Checks.point252
  · exact Block2Checks.point253
  · exact Block2Checks.point254
  · exact Block2Checks.point255
  · exact Block2Checks.point256
  · exact Block2Checks.point257

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
