module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point238
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point239
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point240
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point241
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point242
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point243
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point244
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point245
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point246
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point247
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point248
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point249
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point250
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point251
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point252
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point253
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block2.Point254
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual interval 238–254

Assemble the separately kernel-checked permutation identities in this interval.
Source: `OrderLevel0Part3ResidualReduction.target` and `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks

public theorem block2 : subbatch 2 := by
  intro s hs
  fin_cases s
  · exact point238
  · exact point239
  · exact point240
  · exact point241
  · exact point242
  · exact point243
  · exact point244
  · exact point245
  · exact point246
  · exact point247
  · exact point248
  · exact point249
  · exact point250
  · exact point251
  · exact point252
  · exact point253
  · exact point254

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
