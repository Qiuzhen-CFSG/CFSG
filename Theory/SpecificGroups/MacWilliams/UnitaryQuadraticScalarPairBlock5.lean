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

@[expose] public def scalarPairBlock5 : List (Fin 1024) :=
  [700, 701, 703, 707, 710, 713, 717, 718, 719, 738, 743, 745, 749, 750, 751, 787, 789, 795, 796, 798, 799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_700 : scalarRowCheck 700 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_701 : scalarRowCheck 701 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_703 : scalarRowCheck 703 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_707 : scalarRowCheck 707 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_710 : scalarRowCheck 710 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_713 : scalarRowCheck 713 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_717 : scalarRowCheck 717 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_718 : scalarRowCheck 718 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_719 : scalarRowCheck 719 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_738 : scalarRowCheck 738 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_743 : scalarRowCheck 743 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_745 : scalarRowCheck 745 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_749 : scalarRowCheck 749 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_750 : scalarRowCheck 750 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_751 : scalarRowCheck 751 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_787 : scalarRowCheck 787 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_789 : scalarRowCheck 789 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_795 : scalarRowCheck 795 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_796 : scalarRowCheck 796 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_798 : scalarRowCheck 798 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_799 : scalarRowCheck 799 = true := by decide +kernel

public theorem scalar_pair_block_5 :
    (scalarPairBlock5.all scalarRowCheck) = true := by
  simp only [scalarPairBlock5, List.all_cons, List.all_nil,
    row_700, row_701, row_703, row_707, row_710, row_713, row_717, row_718, row_719, row_738, row_743, row_745, row_749, row_750, row_751, row_787, row_789, row_795, row_796, row_798, row_799, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

