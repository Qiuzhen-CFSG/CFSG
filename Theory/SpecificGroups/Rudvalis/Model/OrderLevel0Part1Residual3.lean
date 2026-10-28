module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual3.Points6
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-1 residual certificate, indices 213–282

The certified composition tables establish all 70 original transitions.
Enumerating the prescribed residual indices gives exactly `residualBatch 3`.
Source: `OrderLevel0Data` and `Part1Residual.target`; table certification
reuses `OrderLevel0Part6Block2` and checks each additional composition.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual

/-- The final residual batch in the part-1 order certificate. -/
public theorem residuals3 : residualBatch 3 := by
  intro s hs
  fin_cases s
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
  · exact Residual3.point259
  · exact Residual3.point260
  · exact Residual3.point261
  · exact Residual3.point262
  · exact Residual3.point263
  · exact Residual3.point264
  · exact Residual3.point265
  · exact Residual3.point266
  · exact Residual3.point267
  · exact Residual3.point268
  · exact Residual3.point269
  · exact Residual3.point270
  · exact Residual3.point271
  · exact Residual3.point272
  · exact Residual3.point273
  · exact Residual3.point274
  · exact Residual3.point275
  · exact Residual3.point276
  · exact Residual3.point277
  · exact Residual3.point278
  · exact Residual3.point279
  · exact Residual3.point280
  · exact Residual3.point281
  · exact Residual3.point282
  · change 283 < 283 at hs
    omega

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual
