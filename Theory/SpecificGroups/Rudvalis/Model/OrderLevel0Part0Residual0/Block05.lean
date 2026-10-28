module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 25–29

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point25Slice0 : pointSliceCheck 0 1276 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice1 : pointSliceCheck 0 1276 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice2 : pointSliceCheck 0 1276 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice3 : pointSliceCheck 0 1276 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice4 : pointSliceCheck 0 1276 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice5 : pointSliceCheck 0 1276 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice6 : pointSliceCheck 0 1276 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice7 : pointSliceCheck 0 1276 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice8 : pointSliceCheck 0 1276 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice9 : pointSliceCheck 0 1276 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice10 : pointSliceCheck 0 1276 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice11 : pointSliceCheck 0 1276 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice12 : pointSliceCheck 0 1276 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice13 : pointSliceCheck 0 1276 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice14 : pointSliceCheck 0 1276 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice15 : pointSliceCheck 0 1276 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice16 : pointSliceCheck 0 1276 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice17 : pointSliceCheck 0 1276 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice18 : pointSliceCheck 0 1276 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice19 : pointSliceCheck 0 1276 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice20 : pointSliceCheck 0 1276 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice21 : pointSliceCheck 0 1276 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice22 : pointSliceCheck 0 1276 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice23 : pointSliceCheck 0 1276 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice24 : pointSliceCheck 0 1276 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice25 : pointSliceCheck 0 1276 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice26 : pointSliceCheck 0 1276 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice27 : pointSliceCheck 0 1276 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25Slice28 : pointSliceCheck 0 1276 28 := by
  decide +kernel

public theorem point25 : residualCheck 25 := by
  apply ofPointSlices 0 1276
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
private theorem point26Slice0 : pointSliceCheck 1 1262 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice1 : pointSliceCheck 1 1262 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice2 : pointSliceCheck 1 1262 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice3 : pointSliceCheck 1 1262 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice4 : pointSliceCheck 1 1262 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice5 : pointSliceCheck 1 1262 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice6 : pointSliceCheck 1 1262 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice7 : pointSliceCheck 1 1262 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice8 : pointSliceCheck 1 1262 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice9 : pointSliceCheck 1 1262 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice10 : pointSliceCheck 1 1262 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice11 : pointSliceCheck 1 1262 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice12 : pointSliceCheck 1 1262 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice13 : pointSliceCheck 1 1262 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice14 : pointSliceCheck 1 1262 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice15 : pointSliceCheck 1 1262 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice16 : pointSliceCheck 1 1262 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice17 : pointSliceCheck 1 1262 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice18 : pointSliceCheck 1 1262 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice19 : pointSliceCheck 1 1262 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice20 : pointSliceCheck 1 1262 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice21 : pointSliceCheck 1 1262 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice22 : pointSliceCheck 1 1262 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice23 : pointSliceCheck 1 1262 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice24 : pointSliceCheck 1 1262 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice25 : pointSliceCheck 1 1262 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice26 : pointSliceCheck 1 1262 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice27 : pointSliceCheck 1 1262 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26Slice28 : pointSliceCheck 1 1262 28 := by
  decide +kernel

public theorem point26 : residualCheck 26 := by
  apply ofPointSlices 1 1262
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
private theorem point27Slice0 : pointSliceCheck 1 1268 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice1 : pointSliceCheck 1 1268 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice2 : pointSliceCheck 1 1268 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice3 : pointSliceCheck 1 1268 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice4 : pointSliceCheck 1 1268 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice5 : pointSliceCheck 1 1268 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice6 : pointSliceCheck 1 1268 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice7 : pointSliceCheck 1 1268 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice8 : pointSliceCheck 1 1268 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice9 : pointSliceCheck 1 1268 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice10 : pointSliceCheck 1 1268 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice11 : pointSliceCheck 1 1268 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice12 : pointSliceCheck 1 1268 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice13 : pointSliceCheck 1 1268 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice14 : pointSliceCheck 1 1268 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice15 : pointSliceCheck 1 1268 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice16 : pointSliceCheck 1 1268 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice17 : pointSliceCheck 1 1268 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice18 : pointSliceCheck 1 1268 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice19 : pointSliceCheck 1 1268 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice20 : pointSliceCheck 1 1268 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice21 : pointSliceCheck 1 1268 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice22 : pointSliceCheck 1 1268 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice23 : pointSliceCheck 1 1268 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice24 : pointSliceCheck 1 1268 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice25 : pointSliceCheck 1 1268 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice26 : pointSliceCheck 1 1268 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice27 : pointSliceCheck 1 1268 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27Slice28 : pointSliceCheck 1 1268 28 := by
  decide +kernel

public theorem point27 : residualCheck 27 := by
  apply ofPointSlices 1 1268
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
private theorem point28Slice0 : pointSliceCheck 1 1270 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice1 : pointSliceCheck 1 1270 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice2 : pointSliceCheck 1 1270 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice3 : pointSliceCheck 1 1270 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice4 : pointSliceCheck 1 1270 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice5 : pointSliceCheck 1 1270 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice6 : pointSliceCheck 1 1270 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice7 : pointSliceCheck 1 1270 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice8 : pointSliceCheck 1 1270 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice9 : pointSliceCheck 1 1270 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice10 : pointSliceCheck 1 1270 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice11 : pointSliceCheck 1 1270 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice12 : pointSliceCheck 1 1270 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice13 : pointSliceCheck 1 1270 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice14 : pointSliceCheck 1 1270 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice15 : pointSliceCheck 1 1270 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice16 : pointSliceCheck 1 1270 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice17 : pointSliceCheck 1 1270 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice18 : pointSliceCheck 1 1270 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice19 : pointSliceCheck 1 1270 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice20 : pointSliceCheck 1 1270 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice21 : pointSliceCheck 1 1270 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice22 : pointSliceCheck 1 1270 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice23 : pointSliceCheck 1 1270 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice24 : pointSliceCheck 1 1270 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice25 : pointSliceCheck 1 1270 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice26 : pointSliceCheck 1 1270 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice27 : pointSliceCheck 1 1270 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28Slice28 : pointSliceCheck 1 1270 28 := by
  decide +kernel

public theorem point28 : residualCheck 28 := by
  apply ofPointSlices 1 1270
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
private theorem point29Slice0 : pointSliceCheck 0 1404 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice1 : pointSliceCheck 0 1404 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice2 : pointSliceCheck 0 1404 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice3 : pointSliceCheck 0 1404 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice4 : pointSliceCheck 0 1404 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice5 : pointSliceCheck 0 1404 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice6 : pointSliceCheck 0 1404 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice7 : pointSliceCheck 0 1404 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice8 : pointSliceCheck 0 1404 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice9 : pointSliceCheck 0 1404 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice10 : pointSliceCheck 0 1404 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice11 : pointSliceCheck 0 1404 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice12 : pointSliceCheck 0 1404 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice13 : pointSliceCheck 0 1404 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice14 : pointSliceCheck 0 1404 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice15 : pointSliceCheck 0 1404 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice16 : pointSliceCheck 0 1404 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice17 : pointSliceCheck 0 1404 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice18 : pointSliceCheck 0 1404 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice19 : pointSliceCheck 0 1404 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice20 : pointSliceCheck 0 1404 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice21 : pointSliceCheck 0 1404 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice22 : pointSliceCheck 0 1404 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice23 : pointSliceCheck 0 1404 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice24 : pointSliceCheck 0 1404 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice25 : pointSliceCheck 0 1404 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice26 : pointSliceCheck 0 1404 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice27 : pointSliceCheck 0 1404 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point29Slice28 : pointSliceCheck 0 1404 28 := by
  decide +kernel

public theorem point29 : residualCheck 29 := by
  apply ofPointSlices 0 1404
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

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
