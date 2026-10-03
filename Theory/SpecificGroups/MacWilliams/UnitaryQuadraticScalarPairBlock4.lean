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

@[expose] public def scalarPairBlock4 : List (Fin 1024) :=
  [595, 599, 601, 604, 606, 607, 627, 631, 632, 637, 638, 639, 659, 662, 667, 668, 669, 671, 690, 695, 699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_595 : scalarRowCheck 595 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_599 : scalarRowCheck 599 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_601 : scalarRowCheck 601 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_604 : scalarRowCheck 604 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_606 : scalarRowCheck 606 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_607 : scalarRowCheck 607 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_627 : scalarRowCheck 627 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_631 : scalarRowCheck 631 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_632 : scalarRowCheck 632 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_637 : scalarRowCheck 637 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_638 : scalarRowCheck 638 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_639 : scalarRowCheck 639 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_659 : scalarRowCheck 659 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_662 : scalarRowCheck 662 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_667 : scalarRowCheck 667 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_668 : scalarRowCheck 668 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_669 : scalarRowCheck 669 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_671 : scalarRowCheck 671 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_690 : scalarRowCheck 690 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_695 : scalarRowCheck 695 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_699 : scalarRowCheck 699 = true := by decide +kernel

public theorem scalar_pair_block_4 :
    (scalarPairBlock4.all scalarRowCheck) = true := by
  simp only [scalarPairBlock4, List.all_cons, List.all_nil,
    row_595, row_599, row_601, row_604, row_606, row_607, row_627, row_631, row_632, row_637, row_638, row_639, row_659, row_662, row_667, row_668, row_669, row_671, row_690, row_695, row_699, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

