module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Slices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-1 residual group 0: independently checked transitions

Check the original permutation identities on 29 slices of 140 points and
assemble them with `ofPointSlices`. Separate declarations bound kernel memory.
Source: `OrderLevel0Data` and `OrderLevel0Part1ResidualReduction.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point25Slice0 : pointSliceCheck 1 1290 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice1 : pointSliceCheck 1 1290 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice2 : pointSliceCheck 1 1290 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice3 : pointSliceCheck 1 1290 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice4 : pointSliceCheck 1 1290 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice5 : pointSliceCheck 1 1290 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice6 : pointSliceCheck 1 1290 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice7 : pointSliceCheck 1 1290 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice8 : pointSliceCheck 1 1290 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice9 : pointSliceCheck 1 1290 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice10 : pointSliceCheck 1 1290 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice11 : pointSliceCheck 1 1290 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice12 : pointSliceCheck 1 1290 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice13 : pointSliceCheck 1 1290 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice14 : pointSliceCheck 1 1290 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice15 : pointSliceCheck 1 1290 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice16 : pointSliceCheck 1 1290 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice17 : pointSliceCheck 1 1290 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice18 : pointSliceCheck 1 1290 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice19 : pointSliceCheck 1 1290 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice20 : pointSliceCheck 1 1290 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice21 : pointSliceCheck 1 1290 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice22 : pointSliceCheck 1 1290 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice23 : pointSliceCheck 1 1290 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice24 : pointSliceCheck 1 1290 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice25 : pointSliceCheck 1 1290 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice26 : pointSliceCheck 1 1290 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice27 : pointSliceCheck 1 1290 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice28 : pointSliceCheck 1 1290 28 := by
  decide +kernel

public theorem point25 : residualCheck 25 := by
  apply ofPointSlices 1 1290
  intro c
  fin_cases c
  · exact point25Slice0
  · exact point25Slice1
  · exact point25Slice2
  · exact point25Slice3
  · exact point25Slice4
  · exact point25Slice5
  · exact point25Slice6
  · exact point25Slice7
  · exact point25Slice8
  · exact point25Slice9
  · exact point25Slice10
  · exact point25Slice11
  · exact point25Slice12
  · exact point25Slice13
  · exact point25Slice14
  · exact point25Slice15
  · exact point25Slice16
  · exact point25Slice17
  · exact point25Slice18
  · exact point25Slice19
  · exact point25Slice20
  · exact point25Slice21
  · exact point25Slice22
  · exact point25Slice23
  · exact point25Slice24
  · exact point25Slice25
  · exact point25Slice26
  · exact point25Slice27
  · exact point25Slice28

set_option maxHeartbeats 1600000 in
private theorem point26Slice0 : pointSliceCheck 1 1291 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice1 : pointSliceCheck 1 1291 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice2 : pointSliceCheck 1 1291 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice3 : pointSliceCheck 1 1291 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice4 : pointSliceCheck 1 1291 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice5 : pointSliceCheck 1 1291 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice6 : pointSliceCheck 1 1291 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice7 : pointSliceCheck 1 1291 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice8 : pointSliceCheck 1 1291 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice9 : pointSliceCheck 1 1291 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice10 : pointSliceCheck 1 1291 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice11 : pointSliceCheck 1 1291 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice12 : pointSliceCheck 1 1291 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice13 : pointSliceCheck 1 1291 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice14 : pointSliceCheck 1 1291 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice15 : pointSliceCheck 1 1291 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice16 : pointSliceCheck 1 1291 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice17 : pointSliceCheck 1 1291 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice18 : pointSliceCheck 1 1291 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice19 : pointSliceCheck 1 1291 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice20 : pointSliceCheck 1 1291 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice21 : pointSliceCheck 1 1291 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice22 : pointSliceCheck 1 1291 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice23 : pointSliceCheck 1 1291 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice24 : pointSliceCheck 1 1291 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice25 : pointSliceCheck 1 1291 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice26 : pointSliceCheck 1 1291 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice27 : pointSliceCheck 1 1291 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice28 : pointSliceCheck 1 1291 28 := by
  decide +kernel

public theorem point26 : residualCheck 26 := by
  apply ofPointSlices 1 1291
  intro c
  fin_cases c
  · exact point26Slice0
  · exact point26Slice1
  · exact point26Slice2
  · exact point26Slice3
  · exact point26Slice4
  · exact point26Slice5
  · exact point26Slice6
  · exact point26Slice7
  · exact point26Slice8
  · exact point26Slice9
  · exact point26Slice10
  · exact point26Slice11
  · exact point26Slice12
  · exact point26Slice13
  · exact point26Slice14
  · exact point26Slice15
  · exact point26Slice16
  · exact point26Slice17
  · exact point26Slice18
  · exact point26Slice19
  · exact point26Slice20
  · exact point26Slice21
  · exact point26Slice22
  · exact point26Slice23
  · exact point26Slice24
  · exact point26Slice25
  · exact point26Slice26
  · exact point26Slice27
  · exact point26Slice28

set_option maxHeartbeats 1600000 in
private theorem point27Slice0 : pointSliceCheck 1 1297 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice1 : pointSliceCheck 1 1297 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice2 : pointSliceCheck 1 1297 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice3 : pointSliceCheck 1 1297 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice4 : pointSliceCheck 1 1297 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice5 : pointSliceCheck 1 1297 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice6 : pointSliceCheck 1 1297 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice7 : pointSliceCheck 1 1297 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice8 : pointSliceCheck 1 1297 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice9 : pointSliceCheck 1 1297 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice10 : pointSliceCheck 1 1297 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice11 : pointSliceCheck 1 1297 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice12 : pointSliceCheck 1 1297 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice13 : pointSliceCheck 1 1297 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice14 : pointSliceCheck 1 1297 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice15 : pointSliceCheck 1 1297 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice16 : pointSliceCheck 1 1297 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice17 : pointSliceCheck 1 1297 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice18 : pointSliceCheck 1 1297 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice19 : pointSliceCheck 1 1297 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice20 : pointSliceCheck 1 1297 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice21 : pointSliceCheck 1 1297 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice22 : pointSliceCheck 1 1297 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice23 : pointSliceCheck 1 1297 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice24 : pointSliceCheck 1 1297 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice25 : pointSliceCheck 1 1297 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice26 : pointSliceCheck 1 1297 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice27 : pointSliceCheck 1 1297 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice28 : pointSliceCheck 1 1297 28 := by
  decide +kernel

public theorem point27 : residualCheck 27 := by
  apply ofPointSlices 1 1297
  intro c
  fin_cases c
  · exact point27Slice0
  · exact point27Slice1
  · exact point27Slice2
  · exact point27Slice3
  · exact point27Slice4
  · exact point27Slice5
  · exact point27Slice6
  · exact point27Slice7
  · exact point27Slice8
  · exact point27Slice9
  · exact point27Slice10
  · exact point27Slice11
  · exact point27Slice12
  · exact point27Slice13
  · exact point27Slice14
  · exact point27Slice15
  · exact point27Slice16
  · exact point27Slice17
  · exact point27Slice18
  · exact point27Slice19
  · exact point27Slice20
  · exact point27Slice21
  · exact point27Slice22
  · exact point27Slice23
  · exact point27Slice24
  · exact point27Slice25
  · exact point27Slice26
  · exact point27Slice27
  · exact point27Slice28

set_option maxHeartbeats 1600000 in
private theorem point28Slice0 : pointSliceCheck 0 1425 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice1 : pointSliceCheck 0 1425 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice2 : pointSliceCheck 0 1425 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice3 : pointSliceCheck 0 1425 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice4 : pointSliceCheck 0 1425 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice5 : pointSliceCheck 0 1425 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice6 : pointSliceCheck 0 1425 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice7 : pointSliceCheck 0 1425 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice8 : pointSliceCheck 0 1425 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice9 : pointSliceCheck 0 1425 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice10 : pointSliceCheck 0 1425 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice11 : pointSliceCheck 0 1425 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice12 : pointSliceCheck 0 1425 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice13 : pointSliceCheck 0 1425 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice14 : pointSliceCheck 0 1425 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice15 : pointSliceCheck 0 1425 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice16 : pointSliceCheck 0 1425 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice17 : pointSliceCheck 0 1425 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice18 : pointSliceCheck 0 1425 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice19 : pointSliceCheck 0 1425 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice20 : pointSliceCheck 0 1425 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice21 : pointSliceCheck 0 1425 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice22 : pointSliceCheck 0 1425 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice23 : pointSliceCheck 0 1425 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice24 : pointSliceCheck 0 1425 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice25 : pointSliceCheck 0 1425 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice26 : pointSliceCheck 0 1425 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice27 : pointSliceCheck 0 1425 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice28 : pointSliceCheck 0 1425 28 := by
  decide +kernel

public theorem point28 : residualCheck 28 := by
  apply ofPointSlices 0 1425
  intro c
  fin_cases c
  · exact point28Slice0
  · exact point28Slice1
  · exact point28Slice2
  · exact point28Slice3
  · exact point28Slice4
  · exact point28Slice5
  · exact point28Slice6
  · exact point28Slice7
  · exact point28Slice8
  · exact point28Slice9
  · exact point28Slice10
  · exact point28Slice11
  · exact point28Slice12
  · exact point28Slice13
  · exact point28Slice14
  · exact point28Slice15
  · exact point28Slice16
  · exact point28Slice17
  · exact point28Slice18
  · exact point28Slice19
  · exact point28Slice20
  · exact point28Slice21
  · exact point28Slice22
  · exact point28Slice23
  · exact point28Slice24
  · exact point28Slice25
  · exact point28Slice26
  · exact point28Slice27
  · exact point28Slice28

set_option maxHeartbeats 1600000 in
private theorem point29Slice0 : pointSliceCheck 0 1434 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice1 : pointSliceCheck 0 1434 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice2 : pointSliceCheck 0 1434 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice3 : pointSliceCheck 0 1434 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice4 : pointSliceCheck 0 1434 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice5 : pointSliceCheck 0 1434 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice6 : pointSliceCheck 0 1434 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice7 : pointSliceCheck 0 1434 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice8 : pointSliceCheck 0 1434 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice9 : pointSliceCheck 0 1434 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice10 : pointSliceCheck 0 1434 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice11 : pointSliceCheck 0 1434 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice12 : pointSliceCheck 0 1434 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice13 : pointSliceCheck 0 1434 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice14 : pointSliceCheck 0 1434 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice15 : pointSliceCheck 0 1434 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice16 : pointSliceCheck 0 1434 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice17 : pointSliceCheck 0 1434 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice18 : pointSliceCheck 0 1434 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice19 : pointSliceCheck 0 1434 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice20 : pointSliceCheck 0 1434 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice21 : pointSliceCheck 0 1434 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice22 : pointSliceCheck 0 1434 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice23 : pointSliceCheck 0 1434 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice24 : pointSliceCheck 0 1434 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice25 : pointSliceCheck 0 1434 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice26 : pointSliceCheck 0 1434 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice27 : pointSliceCheck 0 1434 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice28 : pointSliceCheck 0 1434 28 := by
  decide +kernel

public theorem point29 : residualCheck 29 := by
  apply ofPointSlices 0 1434
  intro c
  fin_cases c
  · exact point29Slice0
  · exact point29Slice1
  · exact point29Slice2
  · exact point29Slice3
  · exact point29Slice4
  · exact point29Slice5
  · exact point29Slice6
  · exact point29Slice7
  · exact point29Slice8
  · exact point29Slice9
  · exact point29Slice10
  · exact point29Slice11
  · exact point29Slice12
  · exact point29Slice13
  · exact point29Slice14
  · exact point29Slice15
  · exact point29Slice16
  · exact point29Slice17
  · exact point29Slice18
  · exact point29Slice19
  · exact point29Slice20
  · exact point29Slice21
  · exact point29Slice22
  · exact point29Slice23
  · exact point29Slice24
  · exact point29Slice25
  · exact point29Slice26
  · exact point29Slice27
  · exact point29Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
