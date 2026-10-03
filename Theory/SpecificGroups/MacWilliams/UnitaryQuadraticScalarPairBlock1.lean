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

@[expose] public def scalarPairBlock1 : List (Fin 1024) :=
  [251, 253, 255, 293, 295, 298, 299, 301, 302, 309, 311, 314, 315, 316, 319, 357, 359, 361, 362, 366, 367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_251 : scalarRowCheck 251 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_253 : scalarRowCheck 253 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_255 : scalarRowCheck 255 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_293 : scalarRowCheck 293 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_295 : scalarRowCheck 295 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_298 : scalarRowCheck 298 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_299 : scalarRowCheck 299 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_301 : scalarRowCheck 301 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_302 : scalarRowCheck 302 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_309 : scalarRowCheck 309 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_311 : scalarRowCheck 311 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_314 : scalarRowCheck 314 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_315 : scalarRowCheck 315 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_316 : scalarRowCheck 316 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_319 : scalarRowCheck 319 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_357 : scalarRowCheck 357 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_359 : scalarRowCheck 359 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_361 : scalarRowCheck 361 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_362 : scalarRowCheck 362 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_366 : scalarRowCheck 366 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_367 : scalarRowCheck 367 = true := by decide +kernel

public theorem scalar_pair_block_1 :
    (scalarPairBlock1.all scalarRowCheck) = true := by
  simp only [scalarPairBlock1, List.all_cons, List.all_nil,
    row_251, row_253, row_255, row_293, row_295, row_298, row_299, row_301, row_302, row_309, row_311, row_314, row_315, row_316, row_319, row_357, row_359, row_361, row_362, row_366, row_367, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

