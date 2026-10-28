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

@[expose] public def scalarPairBlock2 : List (Fin 1024) :=
  [373, 375, 376, 379, 382, 383, 421, 422, 426, 427, 429, 431, 436, 439, 442, 443, 445, 447, 453, 454, 457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_373 : scalarRowCheck 373 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_375 : scalarRowCheck 375 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_376 : scalarRowCheck 376 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_379 : scalarRowCheck 379 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_382 : scalarRowCheck 382 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_383 : scalarRowCheck 383 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_421 : scalarRowCheck 421 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_422 : scalarRowCheck 422 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_426 : scalarRowCheck 426 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_427 : scalarRowCheck 427 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_429 : scalarRowCheck 429 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_431 : scalarRowCheck 431 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_436 : scalarRowCheck 436 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_439 : scalarRowCheck 439 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_442 : scalarRowCheck 442 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_443 : scalarRowCheck 443 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_445 : scalarRowCheck 445 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_447 : scalarRowCheck 447 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_453 : scalarRowCheck 453 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_454 : scalarRowCheck 454 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_457 : scalarRowCheck 457 = true := by decide +kernel

public theorem scalar_pair_block_2 :
    (scalarPairBlock2.all scalarRowCheck) = true := by
  simp only [scalarPairBlock2, List.all_cons, List.all_nil,
    row_373, row_375, row_376, row_379, row_382, row_383, row_421, row_422, row_426, row_427, row_429, row_431, row_436, row_439, row_442, row_443, row_445, row_447, row_453, row_454, row_457, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

