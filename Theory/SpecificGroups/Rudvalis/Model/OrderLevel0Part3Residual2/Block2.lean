module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point170
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point171
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point172
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point173
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point174
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point175
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point176
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point177
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point178
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point179
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point180
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point181
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point182
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point183
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point184
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point185
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2.Block2.Point186
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual group 2: block 2

The seventeen kernel-checked transition certificates prove exactly residual
indices 170 through 186. Their individual modules bound compilation cost;
this theorem matches each certificate to the prescribed residual target.
Source: `OrderLevel0Data` and `Part3Residual.target`, with witness provenance
in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2

public theorem block2 : block 2 := by
  intro s
  fin_cases s
  · exact Block2Checks.point170
  · exact Block2Checks.point171
  · exact Block2Checks.point172
  · exact Block2Checks.point173
  · exact Block2Checks.point174
  · exact Block2Checks.point175
  · exact Block2Checks.point176
  · exact Block2Checks.point177
  · exact Block2Checks.point178
  · exact Block2Checks.point179
  · exact Block2Checks.point180
  · exact Block2Checks.point181
  · exact Block2Checks.point182
  · exact Block2Checks.point183
  · exact Block2Checks.point184
  · exact Block2Checks.point185
  · exact Block2Checks.point186

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
