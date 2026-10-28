module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 240–265 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge240_0 : outer240 * a = (factor9_49 : Model) * outer240 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer240, image_a, image_outer240]
  change outerMatrix240 * matrixA = hMatrixValue factor9_49 * outerMatrix240
  rw [image_factor9_49]
  decide +kernel

public theorem outerEdge240_1 : outer240 * b = (factor0_0 : Model) * outer197 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer240, image_b, image_outer197]
  change outerMatrix240 * matrixB = hMatrixValue factor0_0 * outerMatrix197
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge241_0 : outer241 * a = (factor4_51 : Model) * outer241 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer241, image_a, image_outer241]
  change outerMatrix241 * matrixA = hMatrixValue factor4_51 * outerMatrix241
  rw [image_factor4_51]
  decide +kernel

public theorem outerEdge241_1 : outer241 * b = (factor0_0 : Model) * outer251 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer241, image_b, image_outer251]
  change outerMatrix241 * matrixB = hMatrixValue factor0_0 * outerMatrix251
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge242_0 : outer242 * a = (factor0_0 : Model) * outer223 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer242, image_a, image_outer223]
  change outerMatrix242 * matrixA = hMatrixValue factor0_0 * outerMatrix223
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge242_1 : outer242 * b = (factor0_0 : Model) * outer252 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer242, image_b, image_outer252]
  change outerMatrix242 * matrixB = hMatrixValue factor0_0 * outerMatrix252
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge243_0 : outer243 * a = (factor7_41 : Model) * outer244 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer243, image_a, image_outer244]
  change outerMatrix243 * matrixA = hMatrixValue factor7_41 * outerMatrix244
  rw [image_factor7_41]
  decide +kernel

public theorem outerEdge243_1 : outer243 * b = (factor0_0 : Model) * outer201 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer243, image_b, image_outer201]
  change outerMatrix243 * matrixB = hMatrixValue factor0_0 * outerMatrix201
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge244_0 : outer244 * a = (factor2_38 : Model) * outer243 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer244, image_a, image_outer243]
  change outerMatrix244 * matrixA = hMatrixValue factor2_38 * outerMatrix243
  rw [image_factor2_38]
  decide +kernel

public theorem outerEdge244_1 : outer244 * b = (factor0_0 : Model) * outer203 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer244, image_b, image_outer203]
  change outerMatrix244 * matrixB = hMatrixValue factor0_0 * outerMatrix203
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge245_0 : outer245 * a = (factor0_0 : Model) * outer230 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer245, image_a, image_outer230]
  change outerMatrix245 * matrixA = hMatrixValue factor0_0 * outerMatrix230
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge245_1 : outer245 * b = (factor0_0 : Model) * outer253 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer245, image_b, image_outer253]
  change outerMatrix245 * matrixB = hMatrixValue factor0_0 * outerMatrix253
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge246_0 : outer246 * a = (factor0_0 : Model) * outer231 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer246, image_a, image_outer231]
  change outerMatrix246 * matrixA = hMatrixValue factor0_0 * outerMatrix231
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge246_1 : outer246 * b = (factor0_0 : Model) * outer254 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer246, image_b, image_outer254]
  change outerMatrix246 * matrixB = hMatrixValue factor0_0 * outerMatrix254
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge247_0 : outer247 * a = (factor0_0 : Model) * outer233 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer247, image_a, image_outer233]
  change outerMatrix247 * matrixA = hMatrixValue factor0_0 * outerMatrix233
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge247_1 : outer247 * b = (factor0_0 : Model) * outer255 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer247, image_b, image_outer255]
  change outerMatrix247 * matrixB = hMatrixValue factor0_0 * outerMatrix255
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge248_0 : outer248 * a = (factor0_0 : Model) * outer234 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer248, image_a, image_outer234]
  change outerMatrix248 * matrixA = hMatrixValue factor0_0 * outerMatrix234
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge248_1 : outer248 * b = (factor0_0 : Model) * outer256 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer248, image_b, image_outer256]
  change outerMatrix248 * matrixB = hMatrixValue factor0_0 * outerMatrix256
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge249_0 : outer249 * a = (factor0_23 : Model) * outer250 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer249, image_a, image_outer250]
  change outerMatrix249 * matrixA = hMatrixValue factor0_23 * outerMatrix250
  rw [image_factor0_23]
  decide +kernel

public theorem outerEdge249_1 : outer249 * b = (factor0_0 : Model) * outer214 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer249, image_b, image_outer214]
  change outerMatrix249 * matrixB = hMatrixValue factor0_0 * outerMatrix214
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge250_0 : outer250 * a = (factor9_14 : Model) * outer249 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer250, image_a, image_outer249]
  change outerMatrix250 * matrixA = hMatrixValue factor9_14 * outerMatrix249
  rw [image_factor9_14]
  decide +kernel

public theorem outerEdge250_1 : outer250 * b = (factor0_0 : Model) * outer218 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer250, image_b, image_outer218]
  change outerMatrix250 * matrixB = hMatrixValue factor0_0 * outerMatrix218
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge251_0 : outer251 * a = (factor0_0 : Model) * outer252 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer251, image_a, image_outer252]
  change outerMatrix251 * matrixA = hMatrixValue factor0_0 * outerMatrix252
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge251_1 : outer251 * b = (factor0_0 : Model) * outer222 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer251, image_b, image_outer222]
  change outerMatrix251 * matrixB = hMatrixValue factor0_0 * outerMatrix222
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge252_0 : outer252 * a = (factor0_0 : Model) * outer251 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer252, image_a, image_outer251]
  change outerMatrix252 * matrixA = hMatrixValue factor0_0 * outerMatrix251
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge252_1 : outer252 * b = (factor7_47 : Model) * outer227 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer252, image_b, image_outer227]
  change outerMatrix252 * matrixB = hMatrixValue factor7_47 * outerMatrix227
  rw [image_factor7_47]
  decide +kernel

public theorem outerEdge253_0 : outer253 * a = (factor0_0 : Model) * outer257 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer253, image_a, image_outer257]
  change outerMatrix253 * matrixA = hMatrixValue factor0_0 * outerMatrix257
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge253_1 : outer253 * b = (factor0_0 : Model) * outer258 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer253, image_b, image_outer258]
  change outerMatrix253 * matrixB = hMatrixValue factor0_0 * outerMatrix258
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge254_0 : outer254 * a = (factor0_0 : Model) * outer259 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer254, image_a, image_outer259]
  change outerMatrix254 * matrixA = hMatrixValue factor0_0 * outerMatrix259
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge254_1 : outer254 * b = (factor0_0 : Model) * outer260 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer254, image_b, image_outer260]
  change outerMatrix254 * matrixB = hMatrixValue factor0_0 * outerMatrix260
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge255_0 : outer255 * a = (factor2_15 : Model) * outer256 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer255, image_a, image_outer256]
  change outerMatrix255 * matrixA = hMatrixValue factor2_15 * outerMatrix256
  rw [image_factor2_15]
  decide +kernel

public theorem outerEdge255_1 : outer255 * b = (factor0_0 : Model) * outer261 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer255, image_b, image_outer261]
  change outerMatrix255 * matrixB = hMatrixValue factor0_0 * outerMatrix261
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge256_0 : outer256 * a = (factor0_58 : Model) * outer255 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer256, image_a, image_outer255]
  change outerMatrix256 * matrixA = hMatrixValue factor0_58 * outerMatrix255
  rw [image_factor0_58]
  decide +kernel

public theorem outerEdge256_1 : outer256 * b = (factor0_0 : Model) * outer262 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer256, image_b, image_outer262]
  change outerMatrix256 * matrixB = hMatrixValue factor0_0 * outerMatrix262
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge257_0 : outer257 * a = (factor0_0 : Model) * outer253 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer257, image_a, image_outer253]
  change outerMatrix257 * matrixA = hMatrixValue factor0_0 * outerMatrix253
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge257_1 : outer257 * b = (factor0_0 : Model) * outer263 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer257, image_b, image_outer263]
  change outerMatrix257 * matrixB = hMatrixValue factor0_0 * outerMatrix263
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge258_0 : outer258 * a = (factor10_23 : Model) * outer260 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer258, image_a, image_outer260]
  change outerMatrix258 * matrixA = hMatrixValue factor10_23 * outerMatrix260
  rw [image_factor10_23]
  decide +kernel

public theorem outerEdge258_1 : outer258 * b = (factor0_0 : Model) * outer245 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer258, image_b, image_outer245]
  change outerMatrix258 * matrixB = hMatrixValue factor0_0 * outerMatrix245
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge259_0 : outer259 * a = (factor0_0 : Model) * outer254 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer259, image_a, image_outer254]
  change outerMatrix259 * matrixA = hMatrixValue factor0_0 * outerMatrix254
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge259_1 : outer259 * b = (factor10_23 : Model) * outer259 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer259, image_b, image_outer259]
  change outerMatrix259 * matrixB = hMatrixValue factor10_23 * outerMatrix259
  rw [image_factor10_23]
  decide +kernel

public theorem outerEdge260_0 : outer260 * a = (factor10_34 : Model) * outer258 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer260, image_a, image_outer258]
  change outerMatrix260 * matrixA = hMatrixValue factor10_34 * outerMatrix258
  rw [image_factor10_34]
  decide +kernel

public theorem outerEdge260_1 : outer260 * b = (factor0_0 : Model) * outer246 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer260, image_b, image_outer246]
  change outerMatrix260 * matrixB = hMatrixValue factor0_0 * outerMatrix246
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge261_0 : outer261 * a = (factor0_0 : Model) * outer264 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer261, image_a, image_outer264]
  change outerMatrix261 * matrixA = hMatrixValue factor0_0 * outerMatrix264
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge261_1 : outer261 * b = (factor0_0 : Model) * outer247 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer261, image_b, image_outer247]
  change outerMatrix261 * matrixB = hMatrixValue factor0_0 * outerMatrix247
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge262_0 : outer262 * a = (factor0_0 : Model) * outer265 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer262, image_a, image_outer265]
  change outerMatrix262 * matrixA = hMatrixValue factor0_0 * outerMatrix265
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge262_1 : outer262 * b = (factor0_0 : Model) * outer248 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer262, image_b, image_outer248]
  change outerMatrix262 * matrixB = hMatrixValue factor0_0 * outerMatrix248
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge263_0 : outer263 * a = (factor6_31 : Model) * outer263 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer263, image_a, image_outer263]
  change outerMatrix263 * matrixA = hMatrixValue factor6_31 * outerMatrix263
  rw [image_factor6_31]
  decide +kernel

public theorem outerEdge263_1 : outer263 * b = (factor4_22 : Model) * outer265 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer263, image_b, image_outer265]
  change outerMatrix263 * matrixB = hMatrixValue factor4_22 * outerMatrix265
  rw [image_factor4_22]
  decide +kernel

public theorem outerEdge264_0 : outer264 * a = (factor0_0 : Model) * outer261 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer264, image_a, image_outer261]
  change outerMatrix264 * matrixA = hMatrixValue factor0_0 * outerMatrix261
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge264_1 : outer264 * b = (factor2_15 : Model) * outer264 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer264, image_b, image_outer264]
  change outerMatrix264 * matrixB = hMatrixValue factor2_15 * outerMatrix264
  rw [image_factor2_15]
  decide +kernel

public theorem outerEdge265_0 : outer265 * a = (factor0_0 : Model) * outer262 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer265, image_a, image_outer262]
  change outerMatrix265 * matrixA = hMatrixValue factor0_0 * outerMatrix262
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge265_1 : outer265 * b = (factor6_48 : Model) * outer257 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer265, image_b, image_outer257]
  change outerMatrix265 * matrixB = hMatrixValue factor6_48 * outerMatrix257
  rw [image_factor6_48]
  decide +kernel


end Janko1.OrderCertificate
