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

@[expose] public def scalarPairBlock6 : List (Fin 1024) :=
  [803, 805, 810, 813, 814, 815, 849, 855, 859, 860, 862, 863, 865, 871, 874, 877, 878, 879, 915, 916, 923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_803 : scalarRowCheck 803 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_805 : scalarRowCheck 805 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_810 : scalarRowCheck 810 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_813 : scalarRowCheck 813 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_814 : scalarRowCheck 814 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_815 : scalarRowCheck 815 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_849 : scalarRowCheck 849 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_855 : scalarRowCheck 855 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_859 : scalarRowCheck 859 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_860 : scalarRowCheck 860 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_862 : scalarRowCheck 862 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_863 : scalarRowCheck 863 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_865 : scalarRowCheck 865 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_871 : scalarRowCheck 871 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_874 : scalarRowCheck 874 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_877 : scalarRowCheck 877 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_878 : scalarRowCheck 878 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_879 : scalarRowCheck 879 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_915 : scalarRowCheck 915 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_916 : scalarRowCheck 916 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_923 : scalarRowCheck 923 = true := by decide +kernel

public theorem scalar_pair_block_6 :
    (scalarPairBlock6.all scalarRowCheck) = true := by
  simp only [scalarPairBlock6, List.all_cons, List.all_nil,
    row_803, row_805, row_810, row_813, row_814, row_815, row_849, row_855, row_859, row_860, row_862, row_863, row_865, row_871, row_874, row_877, row_878, row_879, row_915, row_916, row_923, Bool.and_true]

end MacWilliamsSylow.QuadraticCertificate

