module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairChecks

/-!
# A block of the exhaustive scalar-pair certificate

Each row fixes one scalar quadratic code of weight ten and checks all 168
possible partner codes. When their truth tables cover the fifteen nonzero
vectors, the reconstructed coefficient code must occur in the witness list.
All checks use kernel reduction. Splitting the rows bounds checking cost.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def scalarPairBlock0 : List (Fin 1024) :=
  [198, 199, 201, 203, 205, 206, 214, 215, 217, 219, 220, 223, 230, 231, 233, 234, 237, 239, 246, 247, 248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_198 : scalarRowCheck 198 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_199 : scalarRowCheck 199 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_201 : scalarRowCheck 201 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_203 : scalarRowCheck 203 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_205 : scalarRowCheck 205 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_206 : scalarRowCheck 206 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_214 : scalarRowCheck 214 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_215 : scalarRowCheck 215 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_217 : scalarRowCheck 217 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_219 : scalarRowCheck 219 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_220 : scalarRowCheck 220 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_223 : scalarRowCheck 223 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_230 : scalarRowCheck 230 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_231 : scalarRowCheck 231 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_233 : scalarRowCheck 233 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_234 : scalarRowCheck 234 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_237 : scalarRowCheck 237 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_239 : scalarRowCheck 239 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_246 : scalarRowCheck 246 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_247 : scalarRowCheck 247 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_248 : scalarRowCheck 248 = true := by decide +kernel

public theorem scalar_pair_block_0 :
    (scalarPairBlock0.all scalarRowCheck) = true := by
  simp only [scalarPairBlock0, List.all_cons, List.all_nil,
    row_198, row_199, row_201, row_203, row_205, row_206, row_214, row_215, row_217, row_219, row_220, row_223, row_230, row_231, row_233, row_234, row_237, row_239, row_246, row_247, row_248, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

