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
private theorem point15Slice0 : pointSliceCheck 0 1158 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice1 : pointSliceCheck 0 1158 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice2 : pointSliceCheck 0 1158 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice3 : pointSliceCheck 0 1158 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice4 : pointSliceCheck 0 1158 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice5 : pointSliceCheck 0 1158 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice6 : pointSliceCheck 0 1158 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice7 : pointSliceCheck 0 1158 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice8 : pointSliceCheck 0 1158 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice9 : pointSliceCheck 0 1158 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice10 : pointSliceCheck 0 1158 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice11 : pointSliceCheck 0 1158 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice12 : pointSliceCheck 0 1158 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice13 : pointSliceCheck 0 1158 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice14 : pointSliceCheck 0 1158 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice15 : pointSliceCheck 0 1158 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice16 : pointSliceCheck 0 1158 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice17 : pointSliceCheck 0 1158 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice18 : pointSliceCheck 0 1158 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice19 : pointSliceCheck 0 1158 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice20 : pointSliceCheck 0 1158 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice21 : pointSliceCheck 0 1158 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice22 : pointSliceCheck 0 1158 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice23 : pointSliceCheck 0 1158 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice24 : pointSliceCheck 0 1158 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice25 : pointSliceCheck 0 1158 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice26 : pointSliceCheck 0 1158 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice27 : pointSliceCheck 0 1158 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15Slice28 : pointSliceCheck 0 1158 28 := by
  decide +kernel

public theorem point15 : residualCheck 15 := by
  apply ofPointSlices 0 1158
  intro c
  fin_cases c
  · exact point15Slice0
  · exact point15Slice1
  · exact point15Slice2
  · exact point15Slice3
  · exact point15Slice4
  · exact point15Slice5
  · exact point15Slice6
  · exact point15Slice7
  · exact point15Slice8
  · exact point15Slice9
  · exact point15Slice10
  · exact point15Slice11
  · exact point15Slice12
  · exact point15Slice13
  · exact point15Slice14
  · exact point15Slice15
  · exact point15Slice16
  · exact point15Slice17
  · exact point15Slice18
  · exact point15Slice19
  · exact point15Slice20
  · exact point15Slice21
  · exact point15Slice22
  · exact point15Slice23
  · exact point15Slice24
  · exact point15Slice25
  · exact point15Slice26
  · exact point15Slice27
  · exact point15Slice28

set_option maxHeartbeats 1600000 in
private theorem point16Slice0 : pointSliceCheck 1 1141 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice1 : pointSliceCheck 1 1141 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice2 : pointSliceCheck 1 1141 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice3 : pointSliceCheck 1 1141 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice4 : pointSliceCheck 1 1141 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice5 : pointSliceCheck 1 1141 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice6 : pointSliceCheck 1 1141 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice7 : pointSliceCheck 1 1141 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice8 : pointSliceCheck 1 1141 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice9 : pointSliceCheck 1 1141 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice10 : pointSliceCheck 1 1141 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice11 : pointSliceCheck 1 1141 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice12 : pointSliceCheck 1 1141 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice13 : pointSliceCheck 1 1141 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice14 : pointSliceCheck 1 1141 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice15 : pointSliceCheck 1 1141 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice16 : pointSliceCheck 1 1141 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice17 : pointSliceCheck 1 1141 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice18 : pointSliceCheck 1 1141 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice19 : pointSliceCheck 1 1141 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice20 : pointSliceCheck 1 1141 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice21 : pointSliceCheck 1 1141 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice22 : pointSliceCheck 1 1141 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice23 : pointSliceCheck 1 1141 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice24 : pointSliceCheck 1 1141 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice25 : pointSliceCheck 1 1141 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice26 : pointSliceCheck 1 1141 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice27 : pointSliceCheck 1 1141 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16Slice28 : pointSliceCheck 1 1141 28 := by
  decide +kernel

public theorem point16 : residualCheck 16 := by
  apply ofPointSlices 1 1141
  intro c
  fin_cases c
  · exact point16Slice0
  · exact point16Slice1
  · exact point16Slice2
  · exact point16Slice3
  · exact point16Slice4
  · exact point16Slice5
  · exact point16Slice6
  · exact point16Slice7
  · exact point16Slice8
  · exact point16Slice9
  · exact point16Slice10
  · exact point16Slice11
  · exact point16Slice12
  · exact point16Slice13
  · exact point16Slice14
  · exact point16Slice15
  · exact point16Slice16
  · exact point16Slice17
  · exact point16Slice18
  · exact point16Slice19
  · exact point16Slice20
  · exact point16Slice21
  · exact point16Slice22
  · exact point16Slice23
  · exact point16Slice24
  · exact point16Slice25
  · exact point16Slice26
  · exact point16Slice27
  · exact point16Slice28

set_option maxHeartbeats 1600000 in
private theorem point17Slice0 : pointSliceCheck 1 1147 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice1 : pointSliceCheck 1 1147 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice2 : pointSliceCheck 1 1147 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice3 : pointSliceCheck 1 1147 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice4 : pointSliceCheck 1 1147 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice5 : pointSliceCheck 1 1147 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice6 : pointSliceCheck 1 1147 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice7 : pointSliceCheck 1 1147 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice8 : pointSliceCheck 1 1147 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice9 : pointSliceCheck 1 1147 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice10 : pointSliceCheck 1 1147 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice11 : pointSliceCheck 1 1147 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice12 : pointSliceCheck 1 1147 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice13 : pointSliceCheck 1 1147 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice14 : pointSliceCheck 1 1147 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice15 : pointSliceCheck 1 1147 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice16 : pointSliceCheck 1 1147 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice17 : pointSliceCheck 1 1147 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice18 : pointSliceCheck 1 1147 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice19 : pointSliceCheck 1 1147 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice20 : pointSliceCheck 1 1147 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice21 : pointSliceCheck 1 1147 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice22 : pointSliceCheck 1 1147 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice23 : pointSliceCheck 1 1147 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice24 : pointSliceCheck 1 1147 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice25 : pointSliceCheck 1 1147 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice26 : pointSliceCheck 1 1147 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice27 : pointSliceCheck 1 1147 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17Slice28 : pointSliceCheck 1 1147 28 := by
  decide +kernel

public theorem point17 : residualCheck 17 := by
  apply ofPointSlices 1 1147
  intro c
  fin_cases c
  · exact point17Slice0
  · exact point17Slice1
  · exact point17Slice2
  · exact point17Slice3
  · exact point17Slice4
  · exact point17Slice5
  · exact point17Slice6
  · exact point17Slice7
  · exact point17Slice8
  · exact point17Slice9
  · exact point17Slice10
  · exact point17Slice11
  · exact point17Slice12
  · exact point17Slice13
  · exact point17Slice14
  · exact point17Slice15
  · exact point17Slice16
  · exact point17Slice17
  · exact point17Slice18
  · exact point17Slice19
  · exact point17Slice20
  · exact point17Slice21
  · exact point17Slice22
  · exact point17Slice23
  · exact point17Slice24
  · exact point17Slice25
  · exact point17Slice26
  · exact point17Slice27
  · exact point17Slice28

set_option maxHeartbeats 1600000 in
private theorem point18Slice0 : pointSliceCheck 1 1151 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice1 : pointSliceCheck 1 1151 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice2 : pointSliceCheck 1 1151 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice3 : pointSliceCheck 1 1151 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice4 : pointSliceCheck 1 1151 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice5 : pointSliceCheck 1 1151 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice6 : pointSliceCheck 1 1151 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice7 : pointSliceCheck 1 1151 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice8 : pointSliceCheck 1 1151 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice9 : pointSliceCheck 1 1151 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice10 : pointSliceCheck 1 1151 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice11 : pointSliceCheck 1 1151 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice12 : pointSliceCheck 1 1151 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice13 : pointSliceCheck 1 1151 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice14 : pointSliceCheck 1 1151 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice15 : pointSliceCheck 1 1151 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice16 : pointSliceCheck 1 1151 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice17 : pointSliceCheck 1 1151 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice18 : pointSliceCheck 1 1151 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice19 : pointSliceCheck 1 1151 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice20 : pointSliceCheck 1 1151 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice21 : pointSliceCheck 1 1151 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice22 : pointSliceCheck 1 1151 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice23 : pointSliceCheck 1 1151 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice24 : pointSliceCheck 1 1151 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice25 : pointSliceCheck 1 1151 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice26 : pointSliceCheck 1 1151 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice27 : pointSliceCheck 1 1151 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18Slice28 : pointSliceCheck 1 1151 28 := by
  decide +kernel

public theorem point18 : residualCheck 18 := by
  apply ofPointSlices 1 1151
  intro c
  fin_cases c
  · exact point18Slice0
  · exact point18Slice1
  · exact point18Slice2
  · exact point18Slice3
  · exact point18Slice4
  · exact point18Slice5
  · exact point18Slice6
  · exact point18Slice7
  · exact point18Slice8
  · exact point18Slice9
  · exact point18Slice10
  · exact point18Slice11
  · exact point18Slice12
  · exact point18Slice13
  · exact point18Slice14
  · exact point18Slice15
  · exact point18Slice16
  · exact point18Slice17
  · exact point18Slice18
  · exact point18Slice19
  · exact point18Slice20
  · exact point18Slice21
  · exact point18Slice22
  · exact point18Slice23
  · exact point18Slice24
  · exact point18Slice25
  · exact point18Slice26
  · exact point18Slice27
  · exact point18Slice28

set_option maxHeartbeats 1600000 in
private theorem point19Slice0 : pointSliceCheck 0 1282 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice1 : pointSliceCheck 0 1282 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice2 : pointSliceCheck 0 1282 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice3 : pointSliceCheck 0 1282 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice4 : pointSliceCheck 0 1282 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice5 : pointSliceCheck 0 1282 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice6 : pointSliceCheck 0 1282 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice7 : pointSliceCheck 0 1282 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice8 : pointSliceCheck 0 1282 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice9 : pointSliceCheck 0 1282 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice10 : pointSliceCheck 0 1282 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice11 : pointSliceCheck 0 1282 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice12 : pointSliceCheck 0 1282 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice13 : pointSliceCheck 0 1282 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice14 : pointSliceCheck 0 1282 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice15 : pointSliceCheck 0 1282 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice16 : pointSliceCheck 0 1282 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice17 : pointSliceCheck 0 1282 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice18 : pointSliceCheck 0 1282 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice19 : pointSliceCheck 0 1282 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice20 : pointSliceCheck 0 1282 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice21 : pointSliceCheck 0 1282 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice22 : pointSliceCheck 0 1282 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice23 : pointSliceCheck 0 1282 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice24 : pointSliceCheck 0 1282 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice25 : pointSliceCheck 0 1282 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice26 : pointSliceCheck 0 1282 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice27 : pointSliceCheck 0 1282 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19Slice28 : pointSliceCheck 0 1282 28 := by
  decide +kernel

public theorem point19 : residualCheck 19 := by
  apply ofPointSlices 0 1282
  intro c
  fin_cases c
  · exact point19Slice0
  · exact point19Slice1
  · exact point19Slice2
  · exact point19Slice3
  · exact point19Slice4
  · exact point19Slice5
  · exact point19Slice6
  · exact point19Slice7
  · exact point19Slice8
  · exact point19Slice9
  · exact point19Slice10
  · exact point19Slice11
  · exact point19Slice12
  · exact point19Slice13
  · exact point19Slice14
  · exact point19Slice15
  · exact point19Slice16
  · exact point19Slice17
  · exact point19Slice18
  · exact point19Slice19
  · exact point19Slice20
  · exact point19Slice21
  · exact point19Slice22
  · exact point19Slice23
  · exact point19Slice24
  · exact point19Slice25
  · exact point19Slice26
  · exact point19Slice27
  · exact point19Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
