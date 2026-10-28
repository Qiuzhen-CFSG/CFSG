module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block00
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block01
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block02
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block03
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block04
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block05
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block06
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block07
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block08
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block09
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block20
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block21
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3Checks.Block22
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual certificate, indices 216–284

The 69 remaining transitions in residual batch 3 are finite permutation
identities checked in the supporting modules on all 4060 points. The bound
in `residualBatch` excludes the last three indices of `Fin 72`.
Source: `OrderCertificate/GenerateLevel0Part2Residuals.py` and the certified
transition enumeration in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
set_option Elab.async false

/-- The final 69 dense transitions of part 2. -/
public theorem residuals3 : residualBatch 3 := by
  intro s hs
  fin_cases s
  · exact Residual3Checks.point216
  · exact Residual3Checks.point217
  · exact Residual3Checks.point218
  · exact Residual3Checks.point219
  · exact Residual3Checks.point220
  · exact Residual3Checks.point221
  · exact Residual3Checks.point222
  · exact Residual3Checks.point223
  · exact Residual3Checks.point224
  · exact Residual3Checks.point225
  · exact Residual3Checks.point226
  · exact Residual3Checks.point227
  · exact Residual3Checks.point228
  · exact Residual3Checks.point229
  · exact Residual3Checks.point230
  · exact Residual3Checks.point231
  · exact Residual3Checks.point232
  · exact Residual3Checks.point233
  · exact Residual3Checks.point234
  · exact Residual3Checks.point235
  · exact Residual3Checks.point236
  · exact Residual3Checks.point237
  · exact Residual3Checks.point238
  · exact Residual3Checks.point239
  · exact Residual3Checks.point240
  · exact Residual3Checks.point241
  · exact Residual3Checks.point242
  · exact Residual3Checks.point243
  · exact Residual3Checks.point244
  · exact Residual3Checks.point245
  · exact Residual3Checks.point246
  · exact Residual3Checks.point247
  · exact Residual3Checks.point248
  · exact Residual3Checks.point249
  · exact Residual3Checks.point250
  · exact Residual3Checks.point251
  · exact Residual3Checks.point252
  · exact Residual3Checks.point253
  · exact Residual3Checks.point254
  · exact Residual3Checks.point255
  · exact Residual3Checks.point256
  · exact Residual3Checks.point257
  · exact Residual3Checks.point258
  · exact Residual3Checks.point259
  · exact Residual3Checks.point260
  · exact Residual3Checks.point261
  · exact Residual3Checks.point262
  · exact Residual3Checks.point263
  · exact Residual3Checks.point264
  · exact Residual3Checks.point265
  · exact Residual3Checks.point266
  · exact Residual3Checks.point267
  · exact Residual3Checks.point268
  · exact Residual3Checks.point269
  · exact Residual3Checks.point270
  · exact Residual3Checks.point271
  · exact Residual3Checks.point272
  · exact Residual3Checks.point273
  · exact Residual3Checks.point274
  · exact Residual3Checks.point275
  · exact Residual3Checks.point276
  · exact Residual3Checks.point277
  · exact Residual3Checks.point278
  · exact Residual3Checks.point279
  · exact Residual3Checks.point280
  · exact Residual3Checks.point281
  · exact Residual3Checks.point282
  · exact Residual3Checks.point283
  · exact Residual3Checks.point284
  · change 285 < 285 at hs
    omega
  · change 286 < 285 at hs
    omega
  · change 287 < 285 at hs
    omega

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
