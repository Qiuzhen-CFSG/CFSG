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
private theorem point20Slice0 : pointSliceCheck 0 1288 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice1 : pointSliceCheck 0 1288 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice2 : pointSliceCheck 0 1288 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice3 : pointSliceCheck 0 1288 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice4 : pointSliceCheck 0 1288 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice5 : pointSliceCheck 0 1288 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice6 : pointSliceCheck 0 1288 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice7 : pointSliceCheck 0 1288 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice8 : pointSliceCheck 0 1288 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice9 : pointSliceCheck 0 1288 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice10 : pointSliceCheck 0 1288 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice11 : pointSliceCheck 0 1288 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice12 : pointSliceCheck 0 1288 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice13 : pointSliceCheck 0 1288 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice14 : pointSliceCheck 0 1288 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice15 : pointSliceCheck 0 1288 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice16 : pointSliceCheck 0 1288 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice17 : pointSliceCheck 0 1288 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice18 : pointSliceCheck 0 1288 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice19 : pointSliceCheck 0 1288 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice20 : pointSliceCheck 0 1288 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice21 : pointSliceCheck 0 1288 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice22 : pointSliceCheck 0 1288 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice23 : pointSliceCheck 0 1288 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice24 : pointSliceCheck 0 1288 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice25 : pointSliceCheck 0 1288 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice26 : pointSliceCheck 0 1288 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice27 : pointSliceCheck 0 1288 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20Slice28 : pointSliceCheck 0 1288 28 := by
  decide +kernel

public theorem point20 : residualCheck 20 := by
  apply ofPointSlices 0 1288
  intro c
  fin_cases c
  · exact point20Slice0
  · exact point20Slice1
  · exact point20Slice2
  · exact point20Slice3
  · exact point20Slice4
  · exact point20Slice5
  · exact point20Slice6
  · exact point20Slice7
  · exact point20Slice8
  · exact point20Slice9
  · exact point20Slice10
  · exact point20Slice11
  · exact point20Slice12
  · exact point20Slice13
  · exact point20Slice14
  · exact point20Slice15
  · exact point20Slice16
  · exact point20Slice17
  · exact point20Slice18
  · exact point20Slice19
  · exact point20Slice20
  · exact point20Slice21
  · exact point20Slice22
  · exact point20Slice23
  · exact point20Slice24
  · exact point20Slice25
  · exact point20Slice26
  · exact point20Slice27
  · exact point20Slice28

set_option maxHeartbeats 1600000 in
private theorem point21Slice0 : pointSliceCheck 0 1291 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice1 : pointSliceCheck 0 1291 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice2 : pointSliceCheck 0 1291 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice3 : pointSliceCheck 0 1291 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice4 : pointSliceCheck 0 1291 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice5 : pointSliceCheck 0 1291 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice6 : pointSliceCheck 0 1291 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice7 : pointSliceCheck 0 1291 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice8 : pointSliceCheck 0 1291 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice9 : pointSliceCheck 0 1291 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice10 : pointSliceCheck 0 1291 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice11 : pointSliceCheck 0 1291 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice12 : pointSliceCheck 0 1291 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice13 : pointSliceCheck 0 1291 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice14 : pointSliceCheck 0 1291 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice15 : pointSliceCheck 0 1291 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice16 : pointSliceCheck 0 1291 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice17 : pointSliceCheck 0 1291 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice18 : pointSliceCheck 0 1291 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice19 : pointSliceCheck 0 1291 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice20 : pointSliceCheck 0 1291 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice21 : pointSliceCheck 0 1291 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice22 : pointSliceCheck 0 1291 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice23 : pointSliceCheck 0 1291 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice24 : pointSliceCheck 0 1291 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice25 : pointSliceCheck 0 1291 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice26 : pointSliceCheck 0 1291 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice27 : pointSliceCheck 0 1291 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21Slice28 : pointSliceCheck 0 1291 28 := by
  decide +kernel

public theorem point21 : residualCheck 21 := by
  apply ofPointSlices 0 1291
  intro c
  fin_cases c
  · exact point21Slice0
  · exact point21Slice1
  · exact point21Slice2
  · exact point21Slice3
  · exact point21Slice4
  · exact point21Slice5
  · exact point21Slice6
  · exact point21Slice7
  · exact point21Slice8
  · exact point21Slice9
  · exact point21Slice10
  · exact point21Slice11
  · exact point21Slice12
  · exact point21Slice13
  · exact point21Slice14
  · exact point21Slice15
  · exact point21Slice16
  · exact point21Slice17
  · exact point21Slice18
  · exact point21Slice19
  · exact point21Slice20
  · exact point21Slice21
  · exact point21Slice22
  · exact point21Slice23
  · exact point21Slice24
  · exact point21Slice25
  · exact point21Slice26
  · exact point21Slice27
  · exact point21Slice28

set_option maxHeartbeats 1600000 in
private theorem point22Slice0 : pointSliceCheck 0 1293 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice1 : pointSliceCheck 0 1293 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice2 : pointSliceCheck 0 1293 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice3 : pointSliceCheck 0 1293 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice4 : pointSliceCheck 0 1293 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice5 : pointSliceCheck 0 1293 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice6 : pointSliceCheck 0 1293 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice7 : pointSliceCheck 0 1293 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice8 : pointSliceCheck 0 1293 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice9 : pointSliceCheck 0 1293 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice10 : pointSliceCheck 0 1293 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice11 : pointSliceCheck 0 1293 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice12 : pointSliceCheck 0 1293 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice13 : pointSliceCheck 0 1293 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice14 : pointSliceCheck 0 1293 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice15 : pointSliceCheck 0 1293 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice16 : pointSliceCheck 0 1293 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice17 : pointSliceCheck 0 1293 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice18 : pointSliceCheck 0 1293 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice19 : pointSliceCheck 0 1293 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice20 : pointSliceCheck 0 1293 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice21 : pointSliceCheck 0 1293 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice22 : pointSliceCheck 0 1293 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice23 : pointSliceCheck 0 1293 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice24 : pointSliceCheck 0 1293 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice25 : pointSliceCheck 0 1293 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice26 : pointSliceCheck 0 1293 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice27 : pointSliceCheck 0 1293 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22Slice28 : pointSliceCheck 0 1293 28 := by
  decide +kernel

public theorem point22 : residualCheck 22 := by
  apply ofPointSlices 0 1293
  intro c
  fin_cases c
  · exact point22Slice0
  · exact point22Slice1
  · exact point22Slice2
  · exact point22Slice3
  · exact point22Slice4
  · exact point22Slice5
  · exact point22Slice6
  · exact point22Slice7
  · exact point22Slice8
  · exact point22Slice9
  · exact point22Slice10
  · exact point22Slice11
  · exact point22Slice12
  · exact point22Slice13
  · exact point22Slice14
  · exact point22Slice15
  · exact point22Slice16
  · exact point22Slice17
  · exact point22Slice18
  · exact point22Slice19
  · exact point22Slice20
  · exact point22Slice21
  · exact point22Slice22
  · exact point22Slice23
  · exact point22Slice24
  · exact point22Slice25
  · exact point22Slice26
  · exact point22Slice27
  · exact point22Slice28

set_option maxHeartbeats 1600000 in
private theorem point23Slice0 : pointSliceCheck 1 1281 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice1 : pointSliceCheck 1 1281 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice2 : pointSliceCheck 1 1281 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice3 : pointSliceCheck 1 1281 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice4 : pointSliceCheck 1 1281 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice5 : pointSliceCheck 1 1281 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice6 : pointSliceCheck 1 1281 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice7 : pointSliceCheck 1 1281 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice8 : pointSliceCheck 1 1281 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice9 : pointSliceCheck 1 1281 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice10 : pointSliceCheck 1 1281 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice11 : pointSliceCheck 1 1281 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice12 : pointSliceCheck 1 1281 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice13 : pointSliceCheck 1 1281 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice14 : pointSliceCheck 1 1281 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice15 : pointSliceCheck 1 1281 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice16 : pointSliceCheck 1 1281 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice17 : pointSliceCheck 1 1281 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice18 : pointSliceCheck 1 1281 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice19 : pointSliceCheck 1 1281 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice20 : pointSliceCheck 1 1281 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice21 : pointSliceCheck 1 1281 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice22 : pointSliceCheck 1 1281 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice23 : pointSliceCheck 1 1281 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice24 : pointSliceCheck 1 1281 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice25 : pointSliceCheck 1 1281 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice26 : pointSliceCheck 1 1281 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice27 : pointSliceCheck 1 1281 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23Slice28 : pointSliceCheck 1 1281 28 := by
  decide +kernel

public theorem point23 : residualCheck 23 := by
  apply ofPointSlices 1 1281
  intro c
  fin_cases c
  · exact point23Slice0
  · exact point23Slice1
  · exact point23Slice2
  · exact point23Slice3
  · exact point23Slice4
  · exact point23Slice5
  · exact point23Slice6
  · exact point23Slice7
  · exact point23Slice8
  · exact point23Slice9
  · exact point23Slice10
  · exact point23Slice11
  · exact point23Slice12
  · exact point23Slice13
  · exact point23Slice14
  · exact point23Slice15
  · exact point23Slice16
  · exact point23Slice17
  · exact point23Slice18
  · exact point23Slice19
  · exact point23Slice20
  · exact point23Slice21
  · exact point23Slice22
  · exact point23Slice23
  · exact point23Slice24
  · exact point23Slice25
  · exact point23Slice26
  · exact point23Slice27
  · exact point23Slice28

set_option maxHeartbeats 1600000 in
private theorem point24Slice0 : pointSliceCheck 1 1284 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice1 : pointSliceCheck 1 1284 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice2 : pointSliceCheck 1 1284 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice3 : pointSliceCheck 1 1284 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice4 : pointSliceCheck 1 1284 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice5 : pointSliceCheck 1 1284 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice6 : pointSliceCheck 1 1284 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice7 : pointSliceCheck 1 1284 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice8 : pointSliceCheck 1 1284 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice9 : pointSliceCheck 1 1284 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice10 : pointSliceCheck 1 1284 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice11 : pointSliceCheck 1 1284 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice12 : pointSliceCheck 1 1284 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice13 : pointSliceCheck 1 1284 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice14 : pointSliceCheck 1 1284 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice15 : pointSliceCheck 1 1284 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice16 : pointSliceCheck 1 1284 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice17 : pointSliceCheck 1 1284 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice18 : pointSliceCheck 1 1284 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice19 : pointSliceCheck 1 1284 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice20 : pointSliceCheck 1 1284 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice21 : pointSliceCheck 1 1284 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice22 : pointSliceCheck 1 1284 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice23 : pointSliceCheck 1 1284 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice24 : pointSliceCheck 1 1284 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice25 : pointSliceCheck 1 1284 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice26 : pointSliceCheck 1 1284 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice27 : pointSliceCheck 1 1284 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24Slice28 : pointSliceCheck 1 1284 28 := by
  decide +kernel

public theorem point24 : residualCheck 24 := by
  apply ofPointSlices 1 1284
  intro c
  fin_cases c
  · exact point24Slice0
  · exact point24Slice1
  · exact point24Slice2
  · exact point24Slice3
  · exact point24Slice4
  · exact point24Slice5
  · exact point24Slice6
  · exact point24Slice7
  · exact point24Slice8
  · exact point24Slice9
  · exact point24Slice10
  · exact point24Slice11
  · exact point24Slice12
  · exact point24Slice13
  · exact point24Slice14
  · exact point24Slice15
  · exact point24Slice16
  · exact point24Slice17
  · exact point24Slice18
  · exact point24Slice19
  · exact point24Slice20
  · exact point24Slice21
  · exact point24Slice22
  · exact point24Slice23
  · exact point24Slice24
  · exact point24Slice25
  · exact point24Slice26
  · exact point24Slice27
  · exact point24Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
