module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3.Checks12
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual transitions 195–258

The finite certificates establish each original fixed transition. The last
element of `Fin 65` is excluded by the bound in `residualBatch`.
Source: `OrderLevel0Data` and `Part0Residual.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual

/-- The original transition certificates at residual indices 195 through 258. -/
public theorem residuals3 : residualBatch 3 := by
  intro s hs
  fin_cases s
  · exact Residual3.point195
  · exact Residual3.point196
  · exact Residual3.point197
  · exact Residual3.point198
  · exact Residual3.point199
  · exact Residual3.point200
  · exact Residual3.point201
  · exact Residual3.point202
  · exact Residual3.point203
  · exact Residual3.point204
  · exact Residual3.point205
  · exact Residual3.point206
  · exact Residual3.point207
  · exact Residual3.point208
  · exact Residual3.point209
  · exact Residual3.point210
  · exact Residual3.point211
  · exact Residual3.point212
  · exact Residual3.point213
  · exact Residual3.point214
  · exact Residual3.point215
  · exact Residual3.point216
  · exact Residual3.point217
  · exact Residual3.point218
  · exact Residual3.point219
  · exact Residual3.point220
  · exact Residual3.point221
  · exact Residual3.point222
  · exact Residual3.point223
  · exact Residual3.point224
  · exact Residual3.point225
  · exact Residual3.point226
  · exact Residual3.point227
  · exact Residual3.point228
  · exact Residual3.point229
  · exact Residual3.point230
  · exact Residual3.point231
  · exact Residual3.point232
  · exact Residual3.point233
  · exact Residual3.point234
  · exact Residual3.point235
  · exact Residual3.point236
  · exact Residual3.point237
  · exact Residual3.point238
  · exact Residual3.point239
  · exact Residual3.point240
  · exact Residual3.point241
  · exact Residual3.point242
  · exact Residual3.point243
  · exact Residual3.point244
  · exact Residual3.point245
  · exact Residual3.point246
  · exact Residual3.point247
  · exact Residual3.point248
  · exact Residual3.point249
  · exact Residual3.point250
  · exact Residual3.point251
  · exact Residual3.point252
  · exact Residual3.point253
  · exact Residual3.point254
  · exact Residual3.point255
  · exact Residual3.point256
  · exact Residual3.point257
  · exact Residual3.point258
  · exact False.elim (Nat.lt_irrefl 259 hs)

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
