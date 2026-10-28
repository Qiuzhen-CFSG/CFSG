module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Point162
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point153
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point154
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point155
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point156
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point157
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point158
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point159
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point160
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point161
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point163
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point164
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point165
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point166
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point167
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point168
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block1.Point169
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual group 2: block 1

Certify residual indices 153 through 169 using the prescribed forward-generator
identities. Each transition is checked on 203 slices of 20 points in its own
module, bounding the cost of a compilation unit. Transition 162 reuses the
existing certificate. Source: `OrderLevel0Data` and `Part3Residual.target`;
witness provenance is documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2

public theorem block1 : block 1 := by
  intro s
  fin_cases s
  · exact Block1Checks.point153
  · exact Block1Checks.point154
  · exact Block1Checks.point155
  · exact Block1Checks.point156
  · exact Block1Checks.point157
  · exact Block1Checks.point158
  · exact Block1Checks.point159
  · exact Block1Checks.point160
  · exact Block1Checks.point161
  · exact point162
  · exact Block1Checks.point163
  · exact Block1Checks.point164
  · exact Block1Checks.point165
  · exact Block1Checks.point166
  · exact Block1Checks.point167
  · exact Block1Checks.point168
  · exact Block1Checks.point169

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
