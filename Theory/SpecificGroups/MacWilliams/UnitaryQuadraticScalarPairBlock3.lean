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

@[expose] public def scalarPairBlock3 : List (Fin 1024) :=
  [459, 462, 463, 468, 471, 473, 475, 478, 479, 531, 535, 539, 540, 541, 542, 563, 567, 570, 572, 573, 575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_459 : scalarRowCheck 459 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_462 : scalarRowCheck 462 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_463 : scalarRowCheck 463 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_468 : scalarRowCheck 468 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_471 : scalarRowCheck 471 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_473 : scalarRowCheck 473 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_475 : scalarRowCheck 475 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_478 : scalarRowCheck 478 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_479 : scalarRowCheck 479 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_531 : scalarRowCheck 531 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_535 : scalarRowCheck 535 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_539 : scalarRowCheck 539 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_540 : scalarRowCheck 540 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_541 : scalarRowCheck 541 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_542 : scalarRowCheck 542 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_563 : scalarRowCheck 563 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_567 : scalarRowCheck 567 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_570 : scalarRowCheck 570 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_572 : scalarRowCheck 572 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_573 : scalarRowCheck 573 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_575 : scalarRowCheck 575 = true := by decide +kernel

public theorem scalar_pair_block_3 :
    (scalarPairBlock3.all scalarRowCheck) = true := by
  simp only [scalarPairBlock3, List.all_cons, List.all_nil,
    row_459, row_462, row_463, row_468, row_471, row_473, row_475, row_478, row_479, row_531, row_535, row_539, row_540, row_541, row_542, row_563, row_567, row_570, row_572, row_573, row_575, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

