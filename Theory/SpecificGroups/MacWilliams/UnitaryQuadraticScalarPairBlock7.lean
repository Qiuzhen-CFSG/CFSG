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

@[expose] public def scalarPairBlock7 : List (Fin 1024) :=
  [925, 926, 927, 930, 933, 939, 941, 942, 943, 961, 966, 971, 973, 974, 975, 1008, 1015, 1019, 1021, 1022, 1023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_925 : scalarRowCheck 925 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_926 : scalarRowCheck 926 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_927 : scalarRowCheck 927 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_930 : scalarRowCheck 930 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_933 : scalarRowCheck 933 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_939 : scalarRowCheck 939 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_941 : scalarRowCheck 941 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_942 : scalarRowCheck 942 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_943 : scalarRowCheck 943 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_961 : scalarRowCheck 961 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_966 : scalarRowCheck 966 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_971 : scalarRowCheck 971 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_973 : scalarRowCheck 973 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_974 : scalarRowCheck 974 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_975 : scalarRowCheck 975 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1008 : scalarRowCheck 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1015 : scalarRowCheck 1015 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1019 : scalarRowCheck 1019 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1021 : scalarRowCheck 1021 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1022 : scalarRowCheck 1022 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_1023 : scalarRowCheck 1023 = true := by decide +kernel

public theorem scalar_pair_block_7 :
    (scalarPairBlock7.all scalarRowCheck) = true := by
  simp only [scalarPairBlock7, List.all_cons, List.all_nil,
    row_925, row_926, row_927, row_930, row_933, row_939, row_941, row_942, row_943, row_961, row_966, row_971, row_973, row_974, row_975, row_1008, row_1015, row_1019, row_1021, row_1022, row_1023, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

