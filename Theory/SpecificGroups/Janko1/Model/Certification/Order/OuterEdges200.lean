module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 200–239 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge200_0 : outer200 * a = (factor0_0 : Model) * outer222 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer200, image_a, image_outer222]
  change outerMatrix200 * matrixA = hMatrixValue factor0_0 * outerMatrix222
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge200_1 : outer200 * b = (factor0_0 : Model) * outer160 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer200, image_b, image_outer160]
  change outerMatrix200 * matrixB = hMatrixValue factor0_0 * outerMatrix160
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge201_0 : outer201 * a = (factor0_0 : Model) * outer179 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer201, image_a, image_outer179]
  change outerMatrix201 * matrixA = hMatrixValue factor0_0 * outerMatrix179
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge201_1 : outer201 * b = (factor0_0 : Model) * outer223 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer201, image_b, image_outer223]
  change outerMatrix201 * matrixB = hMatrixValue factor0_0 * outerMatrix223
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge202_0 : outer202 * a = (factor0_0 : Model) * outer224 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer202, image_a, image_outer224]
  change outerMatrix202 * matrixA = hMatrixValue factor0_0 * outerMatrix224
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge202_1 : outer202 * b = (factor0_0 : Model) * outer225 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer202, image_b, image_outer225]
  change outerMatrix202 * matrixB = hMatrixValue factor0_0 * outerMatrix225
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge203_0 : outer203 * a = (factor0_0 : Model) * outer181 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer203, image_a, image_outer181]
  change outerMatrix203 * matrixA = hMatrixValue factor0_0 * outerMatrix181
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge203_1 : outer203 * b = (factor0_0 : Model) * outer226 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer203, image_b, image_outer226]
  change outerMatrix203 * matrixB = hMatrixValue factor0_0 * outerMatrix226
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge204_0 : outer204 * a = (factor9_17 : Model) * outer204 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer204, image_a, image_outer204]
  change outerMatrix204 * matrixA = hMatrixValue factor9_17 * outerMatrix204
  rw [image_factor9_17]
  decide +kernel

public theorem outerEdge204_1 : outer204 * b = (factor0_0 : Model) * outer164 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer204, image_b, image_outer164]
  change outerMatrix204 * matrixB = hMatrixValue factor0_0 * outerMatrix164
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge205_0 : outer205 * a = (factor0_0 : Model) * outer227 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer205, image_a, image_outer227]
  change outerMatrix205 * matrixA = hMatrixValue factor0_0 * outerMatrix227
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge205_1 : outer205 * b = (factor0_0 : Model) * outer206 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer205, image_b, image_outer206]
  change outerMatrix205 * matrixB = hMatrixValue factor0_0 * outerMatrix206
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge206_0 : outer206 * a = (factor0_0 : Model) * outer183 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer206, image_a, image_outer183]
  change outerMatrix206 * matrixA = hMatrixValue factor0_0 * outerMatrix183
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge206_1 : outer206 * b = (factor0_0 : Model) * outer182 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer206, image_b, image_outer182]
  change outerMatrix206 * matrixB = hMatrixValue factor0_0 * outerMatrix182
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge207_0 : outer207 * a = (factor0_0 : Model) * outer228 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer207, image_a, image_outer228]
  change outerMatrix207 * matrixA = hMatrixValue factor0_0 * outerMatrix228
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge207_1 : outer207 * b = (factor0_0 : Model) * outer166 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer207, image_b, image_outer166]
  change outerMatrix207 * matrixB = hMatrixValue factor0_0 * outerMatrix166
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge208_0 : outer208 * a = (factor0_0 : Model) * outer229 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer208, image_a, image_outer229]
  change outerMatrix208 * matrixA = hMatrixValue factor0_0 * outerMatrix229
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge208_1 : outer208 * b = (factor0_0 : Model) * outer230 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer208, image_b, image_outer230]
  change outerMatrix208 * matrixB = hMatrixValue factor0_0 * outerMatrix230
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge209_0 : outer209 * a = (factor0_0 : Model) * outer186 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer209, image_a, image_outer186]
  change outerMatrix209 * matrixA = hMatrixValue factor0_0 * outerMatrix186
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge209_1 : outer209 * b = (factor0_0 : Model) * outer231 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer209, image_b, image_outer231]
  change outerMatrix209 * matrixB = hMatrixValue factor0_0 * outerMatrix231
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge210_0 : outer210 * a = (factor0_0 : Model) * outer232 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer210, image_a, image_outer232]
  change outerMatrix210 * matrixA = hMatrixValue factor0_0 * outerMatrix232
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge210_1 : outer210 * b = (factor0_0 : Model) * outer233 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer210, image_b, image_outer233]
  change outerMatrix210 * matrixB = hMatrixValue factor0_0 * outerMatrix233
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge211_0 : outer211 * a = (factor0_0 : Model) * outer188 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer211, image_a, image_outer188]
  change outerMatrix211 * matrixA = hMatrixValue factor0_0 * outerMatrix188
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge211_1 : outer211 * b = (factor0_0 : Model) * outer234 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer211, image_b, image_outer234]
  change outerMatrix211 * matrixB = hMatrixValue factor0_0 * outerMatrix234
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge212_0 : outer212 * a = (factor0_0 : Model) * outer235 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer212, image_a, image_outer235]
  change outerMatrix212 * matrixA = hMatrixValue factor0_0 * outerMatrix235
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge212_1 : outer212 * b = (factor5_28 : Model) * outer229 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer212, image_b, image_outer229]
  change outerMatrix212 * matrixB = hMatrixValue factor5_28 * outerMatrix229
  rw [image_factor5_28]
  decide +kernel

public theorem outerEdge213_0 : outer213 * a = (factor0_0 : Model) * outer190 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer213, image_a, image_outer190]
  change outerMatrix213 * matrixA = hMatrixValue factor0_0 * outerMatrix190
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge213_1 : outer213 * b = (factor0_0 : Model) * outer236 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer213, image_b, image_outer236]
  change outerMatrix213 * matrixB = hMatrixValue factor0_0 * outerMatrix236
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge214_0 : outer214 * a = (factor0_0 : Model) * outer192 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer214, image_a, image_outer192]
  change outerMatrix214 * matrixA = hMatrixValue factor0_0 * outerMatrix192
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge214_1 : outer214 * b = (factor0_0 : Model) * outer237 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer214, image_b, image_outer237]
  change outerMatrix214 * matrixB = hMatrixValue factor0_0 * outerMatrix237
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge215_0 : outer215 * a = (factor0_0 : Model) * outer216 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer215, image_a, image_outer216]
  change outerMatrix215 * matrixA = hMatrixValue factor0_0 * outerMatrix216
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge215_1 : outer215 * b = (factor0_0 : Model) * outer173 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer215, image_b, image_outer173]
  change outerMatrix215 * matrixB = hMatrixValue factor0_0 * outerMatrix173
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge216_0 : outer216 * a = (factor0_0 : Model) * outer215 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer216, image_a, image_outer215]
  change outerMatrix216 * matrixA = hMatrixValue factor0_0 * outerMatrix215
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge216_1 : outer216 * b = (factor0_0 : Model) * outer238 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer216, image_b, image_outer238]
  change outerMatrix216 * matrixB = hMatrixValue factor0_0 * outerMatrix238
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge217_0 : outer217 * a = (factor0_0 : Model) * outer195 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer217, image_a, image_outer195]
  change outerMatrix217 * matrixA = hMatrixValue factor0_0 * outerMatrix195
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge217_1 : outer217 * b = (factor9_35 : Model) * outer217 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer217, image_b, image_outer217]
  change outerMatrix217 * matrixB = hMatrixValue factor9_35 * outerMatrix217
  rw [image_factor9_35]
  decide +kernel

public theorem outerEdge218_0 : outer218 * a = (factor0_0 : Model) * outer196 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer218, image_a, image_outer196]
  change outerMatrix218 * matrixA = hMatrixValue factor0_0 * outerMatrix196
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge218_1 : outer218 * b = (factor0_0 : Model) * outer239 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer218, image_b, image_outer239]
  change outerMatrix218 * matrixB = hMatrixValue factor0_0 * outerMatrix239
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge219_0 : outer219 * a = (factor5_52 : Model) * outer237 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer219, image_a, image_outer237]
  change outerMatrix219 * matrixA = hMatrixValue factor5_52 * outerMatrix237
  rw [image_factor5_52]
  decide +kernel

public theorem outerEdge219_1 : outer219 * b = (factor0_0 : Model) * outer240 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer219, image_b, image_outer240]
  change outerMatrix219 * matrixB = hMatrixValue factor0_0 * outerMatrix240
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge220_0 : outer220 * a = (factor0_0 : Model) * outer198 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer220, image_a, image_outer198]
  change outerMatrix220 * matrixA = hMatrixValue factor0_0 * outerMatrix198
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge220_1 : outer220 * b = (factor10_51 : Model) * outer213 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer220, image_b, image_outer213]
  change outerMatrix220 * matrixB = hMatrixValue factor10_51 * outerMatrix213
  rw [image_factor10_51]
  decide +kernel

public theorem outerEdge221_0 : outer221 * a = (factor10_51 : Model) * outer236 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer221, image_a, image_outer236]
  change outerMatrix221 * matrixA = hMatrixValue factor10_51 * outerMatrix236
  rw [image_factor10_51]
  decide +kernel

public theorem outerEdge221_1 : outer221 * b = (factor1_14 : Model) * outer228 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer221, image_b, image_outer228]
  change outerMatrix221 * matrixB = hMatrixValue factor1_14 * outerMatrix228
  rw [image_factor1_14]
  decide +kernel

public theorem outerEdge222_0 : outer222 * a = (factor0_0 : Model) * outer200 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer222, image_a, image_outer200]
  change outerMatrix222 * matrixA = hMatrixValue factor0_0 * outerMatrix200
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge222_1 : outer222 * b = (factor0_0 : Model) * outer241 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer222, image_b, image_outer241]
  change outerMatrix222 * matrixB = hMatrixValue factor0_0 * outerMatrix241
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge223_0 : outer223 * a = (factor0_0 : Model) * outer242 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer223, image_a, image_outer242]
  change outerMatrix223 * matrixA = hMatrixValue factor0_0 * outerMatrix242
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge223_1 : outer223 * b = (factor0_0 : Model) * outer243 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer223, image_b, image_outer243]
  change outerMatrix223 * matrixB = hMatrixValue factor0_0 * outerMatrix243
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge224_0 : outer224 * a = (factor0_0 : Model) * outer202 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer224, image_a, image_outer202]
  change outerMatrix224 * matrixA = hMatrixValue factor0_0 * outerMatrix202
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge224_1 : outer224 * b = (factor0_6 : Model) * outer224 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer224, image_b, image_outer224]
  change outerMatrix224 * matrixB = hMatrixValue factor0_6 * outerMatrix224
  rw [image_factor0_6]
  decide +kernel

public theorem outerEdge225_0 : outer225 * a = (factor0_0 : Model) * outer226 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer225, image_a, image_outer226]
  change outerMatrix225 * matrixA = hMatrixValue factor0_0 * outerMatrix226
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge225_1 : outer225 * b = (factor0_0 : Model) * outer180 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer225, image_b, image_outer180]
  change outerMatrix225 * matrixB = hMatrixValue factor0_0 * outerMatrix180
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge226_0 : outer226 * a = (factor0_0 : Model) * outer225 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer226, image_a, image_outer225]
  change outerMatrix226 * matrixA = hMatrixValue factor0_0 * outerMatrix225
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge226_1 : outer226 * b = (factor0_0 : Model) * outer244 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer226, image_b, image_outer244]
  change outerMatrix226 * matrixB = hMatrixValue factor0_0 * outerMatrix244
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge227_0 : outer227 * a = (factor0_0 : Model) * outer205 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer227, image_a, image_outer205]
  change outerMatrix227 * matrixA = hMatrixValue factor0_0 * outerMatrix205
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge227_1 : outer227 * b = (factor6_11 : Model) * outer242 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer227, image_b, image_outer242]
  change outerMatrix227 * matrixB = hMatrixValue factor6_11 * outerMatrix242
  rw [image_factor6_11]
  decide +kernel

public theorem outerEdge228_0 : outer228 * a = (factor0_0 : Model) * outer207 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer228, image_a, image_outer207]
  change outerMatrix228 * matrixA = hMatrixValue factor0_0 * outerMatrix207
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge228_1 : outer228 * b = (factor9_6 : Model) * outer199 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer228, image_b, image_outer199]
  change outerMatrix228 * matrixB = hMatrixValue factor9_6 * outerMatrix199
  rw [image_factor9_6]
  decide +kernel

public theorem outerEdge229_0 : outer229 * a = (factor0_0 : Model) * outer208 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer229, image_a, image_outer208]
  change outerMatrix229 * matrixA = hMatrixValue factor0_0 * outerMatrix208
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge229_1 : outer229 * b = (factor4_49 : Model) * outer189 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer229, image_b, image_outer189]
  change outerMatrix229 * matrixB = hMatrixValue factor4_49 * outerMatrix189
  rw [image_factor4_49]
  decide +kernel

public theorem outerEdge230_0 : outer230 * a = (factor0_0 : Model) * outer245 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer230, image_a, image_outer245]
  change outerMatrix230 * matrixA = hMatrixValue factor0_0 * outerMatrix245
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge230_1 : outer230 * b = (factor0_0 : Model) * outer185 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer230, image_b, image_outer185]
  change outerMatrix230 * matrixB = hMatrixValue factor0_0 * outerMatrix185
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge231_0 : outer231 * a = (factor0_0 : Model) * outer246 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer231, image_a, image_outer246]
  change outerMatrix231 * matrixA = hMatrixValue factor0_0 * outerMatrix246
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge231_1 : outer231 * b = (factor0_0 : Model) * outer232 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer231, image_b, image_outer232]
  change outerMatrix231 * matrixB = hMatrixValue factor0_0 * outerMatrix232
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge232_0 : outer232 * a = (factor0_0 : Model) * outer210 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer232, image_a, image_outer210]
  change outerMatrix232 * matrixA = hMatrixValue factor0_0 * outerMatrix210
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge232_1 : outer232 * b = (factor0_0 : Model) * outer209 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer232, image_b, image_outer209]
  change outerMatrix232 * matrixB = hMatrixValue factor0_0 * outerMatrix209
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge233_0 : outer233 * a = (factor0_0 : Model) * outer247 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer233, image_a, image_outer247]
  change outerMatrix233 * matrixA = hMatrixValue factor0_0 * outerMatrix247
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge233_1 : outer233 * b = (factor0_0 : Model) * outer187 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer233, image_b, image_outer187]
  change outerMatrix233 * matrixB = hMatrixValue factor0_0 * outerMatrix187
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge234_0 : outer234 * a = (factor0_0 : Model) * outer248 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer234, image_a, image_outer248]
  change outerMatrix234 * matrixA = hMatrixValue factor0_0 * outerMatrix248
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge234_1 : outer234 * b = (factor5_43 : Model) * outer235 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer234, image_b, image_outer235]
  change outerMatrix234 * matrixB = hMatrixValue factor5_43 * outerMatrix235
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge235_0 : outer235 * a = (factor0_0 : Model) * outer212 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer235, image_a, image_outer212]
  change outerMatrix235 * matrixA = hMatrixValue factor0_0 * outerMatrix212
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge235_1 : outer235 * b = (factor5_43 : Model) * outer211 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer235, image_b, image_outer211]
  change outerMatrix235 * matrixB = hMatrixValue factor5_43 * outerMatrix211
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge236_0 : outer236 * a = (factor9_36 : Model) * outer221 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer236, image_a, image_outer221]
  change outerMatrix236 * matrixA = hMatrixValue factor9_36 * outerMatrix221
  rw [image_factor9_36]
  decide +kernel

public theorem outerEdge236_1 : outer236 * b = (factor9_36 : Model) * outer220 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer236, image_b, image_outer220]
  change outerMatrix236 * matrixB = hMatrixValue factor9_36 * outerMatrix220
  rw [image_factor9_36]
  decide +kernel

public theorem outerEdge237_0 : outer237 * a = (factor8_40 : Model) * outer219 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer237, image_a, image_outer219]
  change outerMatrix237 * matrixA = hMatrixValue factor8_40 * outerMatrix219
  rw [image_factor8_40]
  decide +kernel

public theorem outerEdge237_1 : outer237 * b = (factor0_0 : Model) * outer249 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer237, image_b, image_outer249]
  change outerMatrix237 * matrixB = hMatrixValue factor0_0 * outerMatrix249
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge238_0 : outer238 * a = (factor9_35 : Model) * outer239 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer238, image_a, image_outer239]
  change outerMatrix238 * matrixA = hMatrixValue factor9_35 * outerMatrix239
  rw [image_factor9_35]
  decide +kernel

public theorem outerEdge238_1 : outer238 * b = (factor0_0 : Model) * outer194 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer238, image_b, image_outer194]
  change outerMatrix238 * matrixB = hMatrixValue factor0_0 * outerMatrix194
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge239_0 : outer239 * a = (factor7_56 : Model) * outer238 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer239, image_a, image_outer238]
  change outerMatrix239 * matrixA = hMatrixValue factor7_56 * outerMatrix238
  rw [image_factor7_56]
  decide +kernel

public theorem outerEdge239_1 : outer239 * b = (factor0_0 : Model) * outer250 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer239, image_b, image_outer250]
  change outerMatrix239 * matrixB = hMatrixValue factor0_0 * outerMatrix250
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
