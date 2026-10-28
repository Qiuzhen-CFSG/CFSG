module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2.Checks12
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual transitions 130–194

The cached composition certificates prove the original fixed transition
checks. Source: `OrderLevel0Data` and `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual

/-- The original transition certificates at residual indices 130 through 194. -/
public theorem residuals2 : residualBatch 2 := by
  intro s hs
  fin_cases s
  · exact Cache2.point130
  · exact Cache2.point131
  · exact Cache2.point132
  · exact Cache2.point133
  · exact Cache2.point134
  · exact Cache2.point135
  · exact Cache2.point136
  · exact Cache2.point137
  · exact Cache2.point138
  · exact Cache2.point139
  · exact Cache2.point140
  · exact Cache2.point141
  · exact Cache2.point142
  · exact Cache2.point143
  · exact Cache2.point144
  · exact Cache2.point145
  · exact Cache2.point146
  · exact Cache2.point147
  · exact Cache2.point148
  · exact Cache2.point149
  · exact Cache2.point150
  · exact Cache2.point151
  · exact Cache2.point152
  · exact Cache2.point153
  · exact Cache2.point154
  · exact Cache2.point155
  · exact Cache2.point156
  · exact Cache2.point157
  · exact Cache2.point158
  · exact Cache2.point159
  · exact Cache2.point160
  · exact Cache2.point161
  · exact Cache2.point162
  · exact Cache2.point163
  · exact Cache2.point164
  · exact Cache2.point165
  · exact Cache2.point166
  · exact Cache2.point167
  · exact Cache2.point168
  · exact Cache2.point169
  · exact Cache2.point170
  · exact Cache2.point171
  · exact Cache2.point172
  · exact Cache2.point173
  · exact Cache2.point174
  · exact Cache2.point175
  · exact Cache2.point176
  · exact Cache2.point177
  · exact Cache2.point178
  · exact Cache2.point179
  · exact Cache2.point180
  · exact Cache2.point181
  · exact Cache2.point182
  · exact Cache2.point183
  · exact Cache2.point184
  · exact Cache2.point185
  · exact Cache2.point186
  · exact Cache2.point187
  · exact Cache2.point188
  · exact Cache2.point189
  · exact Cache2.point190
  · exact Cache2.point191
  · exact Cache2.point192
  · exact Cache2.point193
  · exact Cache2.point194

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
