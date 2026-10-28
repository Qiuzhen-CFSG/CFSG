module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2.Block11
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transitions 144–215

Assemble the separately kernel-checked permutation identities for the third
residual batch. The supporting blocks use the generic point-slice interface
from `OrderLevel0Part0ResidualSlices` to check the original representatives and
factor witnesses. Source: `OrderLevel0Data` and `Part2Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
set_option Elab.async false

public theorem residuals2 : residualBatch 2 := by
  intro s hs
  fin_cases s
  · exact Residual2Checks.point144
  · exact Residual2Checks.point145
  · exact Residual2Checks.point146
  · exact Residual2Checks.point147
  · exact Residual2Checks.point148
  · exact Residual2Checks.point149
  · exact Residual2Checks.point150
  · exact Residual2Checks.point151
  · exact Residual2Checks.point152
  · exact Residual2Checks.point153
  · exact Residual2Checks.point154
  · exact Residual2Checks.point155
  · exact Residual2Checks.point156
  · exact Residual2Checks.point157
  · exact Residual2Checks.point158
  · exact Residual2Checks.point159
  · exact Residual2Checks.point160
  · exact Residual2Checks.point161
  · exact Residual2Checks.point162
  · exact Residual2Checks.point163
  · exact Residual2Checks.point164
  · exact Residual2Checks.point165
  · exact Residual2Checks.point166
  · exact Residual2Checks.point167
  · exact Residual2Checks.point168
  · exact Residual2Checks.point169
  · exact Residual2Checks.point170
  · exact Residual2Checks.point171
  · exact Residual2Checks.point172
  · exact Residual2Checks.point173
  · exact Residual2Checks.point174
  · exact Residual2Checks.point175
  · exact Residual2Checks.point176
  · exact Residual2Checks.point177
  · exact Residual2Checks.point178
  · exact Residual2Checks.point179
  · exact Residual2Checks.point180
  · exact Residual2Checks.point181
  · exact Residual2Checks.point182
  · exact Residual2Checks.point183
  · exact Residual2Checks.point184
  · exact Residual2Checks.point185
  · exact Residual2Checks.point186
  · exact Residual2Checks.point187
  · exact Residual2Checks.point188
  · exact Residual2Checks.point189
  · exact Residual2Checks.point190
  · exact Residual2Checks.point191
  · exact Residual2Checks.point192
  · exact Residual2Checks.point193
  · exact Residual2Checks.point194
  · exact Residual2Checks.point195
  · exact Residual2Checks.point196
  · exact Residual2Checks.point197
  · exact Residual2Checks.point198
  · exact Residual2Checks.point199
  · exact Residual2Checks.point200
  · exact Residual2Checks.point201
  · exact Residual2Checks.point202
  · exact Residual2Checks.point203
  · exact Residual2Checks.point204
  · exact Residual2Checks.point205
  · exact Residual2Checks.point206
  · exact Residual2Checks.point207
  · exact Residual2Checks.point208
  · exact Residual2Checks.point209
  · exact Residual2Checks.point210
  · exact Residual2Checks.point211
  · exact Residual2Checks.point212
  · exact Residual2Checks.point213
  · exact Residual2Checks.point214
  · exact Residual2Checks.point215

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
