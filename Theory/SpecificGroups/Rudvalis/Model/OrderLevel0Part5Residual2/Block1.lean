module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point161
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point162
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point163
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point164
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point165
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point166
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point167
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point168
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point169
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point170
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point171
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point172
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point173
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point174
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point175
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point176
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point177
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point178
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point179
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point180
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point181
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point182
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2.Block1.Point183
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-5 residual group 2, block 1

The 23 kernel-checked transitions certify residual indices 161 through 183.
Finite case analysis identifies each transition with its prescribed target.
Source: `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2

public theorem checked1 : block 1 := by
  intro s
  fin_cases s
  · exact Block1.point161
  · exact Block1.point162
  · exact Block1.point163
  · exact Block1.point164
  · exact Block1.point165
  · exact Block1.point166
  · exact Block1.point167
  · exact Block1.point168
  · exact Block1.point169
  · exact Block1.point170
  · exact Block1.point171
  · exact Block1.point172
  · exact Block1.point173
  · exact Block1.point174
  · exact Block1.point175
  · exact Block1.point176
  · exact Block1.point177
  · exact Block1.point178
  · exact Block1.point179
  · exact Block1.point180
  · exact Block1.point181
  · exact Block1.point182
  · exact Block1.point183

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2
