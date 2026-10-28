module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3Assembly
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point204
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point205
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point206
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point207
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point208
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point209
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point210
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point211
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point212
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point213
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point214
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point215
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point216
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point217
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point218
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point219
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3.Block0.Point220
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual interval 204–220

Assemble the separately kernel-checked permutation identities in this interval.
Source: `OrderLevel0Part3ResidualReduction.target` and `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks

public theorem block0 : subbatch 0 := by
  intro s hs
  fin_cases s
  · exact point204
  · exact point205
  · exact point206
  · exact point207
  · exact point208
  · exact point209
  · exact point210
  · exact point211
  · exact point212
  · exact point213
  · exact point214
  · exact point215
  · exact point216
  · exact point217
  · exact point218
  · exact point219
  · exact point220

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
