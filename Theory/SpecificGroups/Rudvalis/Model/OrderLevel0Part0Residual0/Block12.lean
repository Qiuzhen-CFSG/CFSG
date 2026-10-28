module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 60–64

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point60Slice0 : pointSliceCheck 0 1977 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice1 : pointSliceCheck 0 1977 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice2 : pointSliceCheck 0 1977 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice3 : pointSliceCheck 0 1977 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice4 : pointSliceCheck 0 1977 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice5 : pointSliceCheck 0 1977 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice6 : pointSliceCheck 0 1977 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice7 : pointSliceCheck 0 1977 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice8 : pointSliceCheck 0 1977 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice9 : pointSliceCheck 0 1977 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice10 : pointSliceCheck 0 1977 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice11 : pointSliceCheck 0 1977 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice12 : pointSliceCheck 0 1977 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice13 : pointSliceCheck 0 1977 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice14 : pointSliceCheck 0 1977 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice15 : pointSliceCheck 0 1977 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice16 : pointSliceCheck 0 1977 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice17 : pointSliceCheck 0 1977 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice18 : pointSliceCheck 0 1977 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice19 : pointSliceCheck 0 1977 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice20 : pointSliceCheck 0 1977 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice21 : pointSliceCheck 0 1977 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice22 : pointSliceCheck 0 1977 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice23 : pointSliceCheck 0 1977 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice24 : pointSliceCheck 0 1977 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice25 : pointSliceCheck 0 1977 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice26 : pointSliceCheck 0 1977 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice27 : pointSliceCheck 0 1977 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice28 : pointSliceCheck 0 1977 28 := by
  decide +kernel

public theorem point60 : residualCheck 60 := by
  apply ofPointSlices 0 1977
  intro c
  fin_cases c
  · exact point60Slice0
  · exact point60Slice1
  · exact point60Slice2
  · exact point60Slice3
  · exact point60Slice4
  · exact point60Slice5
  · exact point60Slice6
  · exact point60Slice7
  · exact point60Slice8
  · exact point60Slice9
  · exact point60Slice10
  · exact point60Slice11
  · exact point60Slice12
  · exact point60Slice13
  · exact point60Slice14
  · exact point60Slice15
  · exact point60Slice16
  · exact point60Slice17
  · exact point60Slice18
  · exact point60Slice19
  · exact point60Slice20
  · exact point60Slice21
  · exact point60Slice22
  · exact point60Slice23
  · exact point60Slice24
  · exact point60Slice25
  · exact point60Slice26
  · exact point60Slice27
  · exact point60Slice28

set_option maxHeartbeats 1600000 in
private theorem point61Slice0 : pointSliceCheck 1 1969 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice1 : pointSliceCheck 1 1969 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice2 : pointSliceCheck 1 1969 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice3 : pointSliceCheck 1 1969 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice4 : pointSliceCheck 1 1969 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice5 : pointSliceCheck 1 1969 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice6 : pointSliceCheck 1 1969 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice7 : pointSliceCheck 1 1969 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice8 : pointSliceCheck 1 1969 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice9 : pointSliceCheck 1 1969 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice10 : pointSliceCheck 1 1969 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice11 : pointSliceCheck 1 1969 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice12 : pointSliceCheck 1 1969 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice13 : pointSliceCheck 1 1969 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice14 : pointSliceCheck 1 1969 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice15 : pointSliceCheck 1 1969 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice16 : pointSliceCheck 1 1969 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice17 : pointSliceCheck 1 1969 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice18 : pointSliceCheck 1 1969 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice19 : pointSliceCheck 1 1969 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice20 : pointSliceCheck 1 1969 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice21 : pointSliceCheck 1 1969 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice22 : pointSliceCheck 1 1969 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice23 : pointSliceCheck 1 1969 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice24 : pointSliceCheck 1 1969 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice25 : pointSliceCheck 1 1969 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice26 : pointSliceCheck 1 1969 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice27 : pointSliceCheck 1 1969 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice28 : pointSliceCheck 1 1969 28 := by
  decide +kernel

public theorem point61 : residualCheck 61 := by
  apply ofPointSlices 1 1969
  intro c
  fin_cases c
  · exact point61Slice0
  · exact point61Slice1
  · exact point61Slice2
  · exact point61Slice3
  · exact point61Slice4
  · exact point61Slice5
  · exact point61Slice6
  · exact point61Slice7
  · exact point61Slice8
  · exact point61Slice9
  · exact point61Slice10
  · exact point61Slice11
  · exact point61Slice12
  · exact point61Slice13
  · exact point61Slice14
  · exact point61Slice15
  · exact point61Slice16
  · exact point61Slice17
  · exact point61Slice18
  · exact point61Slice19
  · exact point61Slice20
  · exact point61Slice21
  · exact point61Slice22
  · exact point61Slice23
  · exact point61Slice24
  · exact point61Slice25
  · exact point61Slice26
  · exact point61Slice27
  · exact point61Slice28

set_option maxHeartbeats 1600000 in
private theorem point62Slice0 : pointSliceCheck 0 2100 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice1 : pointSliceCheck 0 2100 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice2 : pointSliceCheck 0 2100 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice3 : pointSliceCheck 0 2100 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice4 : pointSliceCheck 0 2100 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice5 : pointSliceCheck 0 2100 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice6 : pointSliceCheck 0 2100 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice7 : pointSliceCheck 0 2100 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice8 : pointSliceCheck 0 2100 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice9 : pointSliceCheck 0 2100 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice10 : pointSliceCheck 0 2100 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice11 : pointSliceCheck 0 2100 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice12 : pointSliceCheck 0 2100 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice13 : pointSliceCheck 0 2100 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice14 : pointSliceCheck 0 2100 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice15 : pointSliceCheck 0 2100 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice16 : pointSliceCheck 0 2100 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice17 : pointSliceCheck 0 2100 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice18 : pointSliceCheck 0 2100 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice19 : pointSliceCheck 0 2100 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice20 : pointSliceCheck 0 2100 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice21 : pointSliceCheck 0 2100 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice22 : pointSliceCheck 0 2100 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice23 : pointSliceCheck 0 2100 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice24 : pointSliceCheck 0 2100 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice25 : pointSliceCheck 0 2100 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice26 : pointSliceCheck 0 2100 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice27 : pointSliceCheck 0 2100 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice28 : pointSliceCheck 0 2100 28 := by
  decide +kernel

public theorem point62 : residualCheck 62 := by
  apply ofPointSlices 0 2100
  intro c
  fin_cases c
  · exact point62Slice0
  · exact point62Slice1
  · exact point62Slice2
  · exact point62Slice3
  · exact point62Slice4
  · exact point62Slice5
  · exact point62Slice6
  · exact point62Slice7
  · exact point62Slice8
  · exact point62Slice9
  · exact point62Slice10
  · exact point62Slice11
  · exact point62Slice12
  · exact point62Slice13
  · exact point62Slice14
  · exact point62Slice15
  · exact point62Slice16
  · exact point62Slice17
  · exact point62Slice18
  · exact point62Slice19
  · exact point62Slice20
  · exact point62Slice21
  · exact point62Slice22
  · exact point62Slice23
  · exact point62Slice24
  · exact point62Slice25
  · exact point62Slice26
  · exact point62Slice27
  · exact point62Slice28

set_option maxHeartbeats 1600000 in
private theorem point63Slice0 : pointSliceCheck 0 2106 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice1 : pointSliceCheck 0 2106 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice2 : pointSliceCheck 0 2106 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice3 : pointSliceCheck 0 2106 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice4 : pointSliceCheck 0 2106 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice5 : pointSliceCheck 0 2106 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice6 : pointSliceCheck 0 2106 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice7 : pointSliceCheck 0 2106 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice8 : pointSliceCheck 0 2106 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice9 : pointSliceCheck 0 2106 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice10 : pointSliceCheck 0 2106 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice11 : pointSliceCheck 0 2106 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice12 : pointSliceCheck 0 2106 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice13 : pointSliceCheck 0 2106 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice14 : pointSliceCheck 0 2106 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice15 : pointSliceCheck 0 2106 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice16 : pointSliceCheck 0 2106 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice17 : pointSliceCheck 0 2106 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice18 : pointSliceCheck 0 2106 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice19 : pointSliceCheck 0 2106 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice20 : pointSliceCheck 0 2106 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice21 : pointSliceCheck 0 2106 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice22 : pointSliceCheck 0 2106 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice23 : pointSliceCheck 0 2106 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice24 : pointSliceCheck 0 2106 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice25 : pointSliceCheck 0 2106 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice26 : pointSliceCheck 0 2106 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice27 : pointSliceCheck 0 2106 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice28 : pointSliceCheck 0 2106 28 := by
  decide +kernel

public theorem point63 : residualCheck 63 := by
  apply ofPointSlices 0 2106
  intro c
  fin_cases c
  · exact point63Slice0
  · exact point63Slice1
  · exact point63Slice2
  · exact point63Slice3
  · exact point63Slice4
  · exact point63Slice5
  · exact point63Slice6
  · exact point63Slice7
  · exact point63Slice8
  · exact point63Slice9
  · exact point63Slice10
  · exact point63Slice11
  · exact point63Slice12
  · exact point63Slice13
  · exact point63Slice14
  · exact point63Slice15
  · exact point63Slice16
  · exact point63Slice17
  · exact point63Slice18
  · exact point63Slice19
  · exact point63Slice20
  · exact point63Slice21
  · exact point63Slice22
  · exact point63Slice23
  · exact point63Slice24
  · exact point63Slice25
  · exact point63Slice26
  · exact point63Slice27
  · exact point63Slice28

set_option maxHeartbeats 1600000 in
private theorem point64Slice0 : pointSliceCheck 0 2114 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice1 : pointSliceCheck 0 2114 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice2 : pointSliceCheck 0 2114 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice3 : pointSliceCheck 0 2114 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice4 : pointSliceCheck 0 2114 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice5 : pointSliceCheck 0 2114 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice6 : pointSliceCheck 0 2114 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice7 : pointSliceCheck 0 2114 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice8 : pointSliceCheck 0 2114 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice9 : pointSliceCheck 0 2114 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice10 : pointSliceCheck 0 2114 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice11 : pointSliceCheck 0 2114 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice12 : pointSliceCheck 0 2114 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice13 : pointSliceCheck 0 2114 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice14 : pointSliceCheck 0 2114 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice15 : pointSliceCheck 0 2114 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice16 : pointSliceCheck 0 2114 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice17 : pointSliceCheck 0 2114 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice18 : pointSliceCheck 0 2114 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice19 : pointSliceCheck 0 2114 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice20 : pointSliceCheck 0 2114 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice21 : pointSliceCheck 0 2114 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice22 : pointSliceCheck 0 2114 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice23 : pointSliceCheck 0 2114 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice24 : pointSliceCheck 0 2114 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice25 : pointSliceCheck 0 2114 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice26 : pointSliceCheck 0 2114 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice27 : pointSliceCheck 0 2114 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice28 : pointSliceCheck 0 2114 28 := by
  decide +kernel

public theorem point64 : residualCheck 64 := by
  apply ofPointSlices 0 2114
  intro c
  fin_cases c
  · exact point64Slice0
  · exact point64Slice1
  · exact point64Slice2
  · exact point64Slice3
  · exact point64Slice4
  · exact point64Slice5
  · exact point64Slice6
  · exact point64Slice7
  · exact point64Slice8
  · exact point64Slice9
  · exact point64Slice10
  · exact point64Slice11
  · exact point64Slice12
  · exact point64Slice13
  · exact point64Slice14
  · exact point64Slice15
  · exact point64Slice16
  · exact point64Slice17
  · exact point64Slice18
  · exact point64Slice19
  · exact point64Slice20
  · exact point64Slice21
  · exact point64Slice22
  · exact point64Slice23
  · exact point64Slice24
  · exact point64Slice25
  · exact point64Slice26
  · exact point64Slice27
  · exact point64Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
