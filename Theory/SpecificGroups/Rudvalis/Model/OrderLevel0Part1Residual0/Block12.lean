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
private theorem point60Slice0 : pointSliceCheck 1 1850 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice1 : pointSliceCheck 1 1850 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice2 : pointSliceCheck 1 1850 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice3 : pointSliceCheck 1 1850 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice4 : pointSliceCheck 1 1850 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice5 : pointSliceCheck 1 1850 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice6 : pointSliceCheck 1 1850 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice7 : pointSliceCheck 1 1850 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice8 : pointSliceCheck 1 1850 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice9 : pointSliceCheck 1 1850 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice10 : pointSliceCheck 1 1850 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice11 : pointSliceCheck 1 1850 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice12 : pointSliceCheck 1 1850 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice13 : pointSliceCheck 1 1850 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice14 : pointSliceCheck 1 1850 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice15 : pointSliceCheck 1 1850 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice16 : pointSliceCheck 1 1850 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice17 : pointSliceCheck 1 1850 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice18 : pointSliceCheck 1 1850 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice19 : pointSliceCheck 1 1850 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice20 : pointSliceCheck 1 1850 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice21 : pointSliceCheck 1 1850 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice22 : pointSliceCheck 1 1850 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice23 : pointSliceCheck 1 1850 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice24 : pointSliceCheck 1 1850 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice25 : pointSliceCheck 1 1850 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice26 : pointSliceCheck 1 1850 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice27 : pointSliceCheck 1 1850 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point60Slice28 : pointSliceCheck 1 1850 28 := by
  decide +kernel

public theorem point60 : residualCheck 60 := by
  apply ofPointSlices 1 1850
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
private theorem point61Slice0 : pointSliceCheck 1 1854 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice1 : pointSliceCheck 1 1854 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice2 : pointSliceCheck 1 1854 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice3 : pointSliceCheck 1 1854 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice4 : pointSliceCheck 1 1854 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice5 : pointSliceCheck 1 1854 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice6 : pointSliceCheck 1 1854 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice7 : pointSliceCheck 1 1854 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice8 : pointSliceCheck 1 1854 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice9 : pointSliceCheck 1 1854 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice10 : pointSliceCheck 1 1854 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice11 : pointSliceCheck 1 1854 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice12 : pointSliceCheck 1 1854 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice13 : pointSliceCheck 1 1854 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice14 : pointSliceCheck 1 1854 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice15 : pointSliceCheck 1 1854 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice16 : pointSliceCheck 1 1854 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice17 : pointSliceCheck 1 1854 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice18 : pointSliceCheck 1 1854 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice19 : pointSliceCheck 1 1854 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice20 : pointSliceCheck 1 1854 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice21 : pointSliceCheck 1 1854 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice22 : pointSliceCheck 1 1854 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice23 : pointSliceCheck 1 1854 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice24 : pointSliceCheck 1 1854 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice25 : pointSliceCheck 1 1854 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice26 : pointSliceCheck 1 1854 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice27 : pointSliceCheck 1 1854 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point61Slice28 : pointSliceCheck 1 1854 28 := by
  decide +kernel

public theorem point61 : residualCheck 61 := by
  apply ofPointSlices 1 1854
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
private theorem point62Slice0 : pointSliceCheck 1 1858 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice1 : pointSliceCheck 1 1858 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice2 : pointSliceCheck 1 1858 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice3 : pointSliceCheck 1 1858 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice4 : pointSliceCheck 1 1858 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice5 : pointSliceCheck 1 1858 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice6 : pointSliceCheck 1 1858 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice7 : pointSliceCheck 1 1858 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice8 : pointSliceCheck 1 1858 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice9 : pointSliceCheck 1 1858 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice10 : pointSliceCheck 1 1858 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice11 : pointSliceCheck 1 1858 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice12 : pointSliceCheck 1 1858 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice13 : pointSliceCheck 1 1858 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice14 : pointSliceCheck 1 1858 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice15 : pointSliceCheck 1 1858 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice16 : pointSliceCheck 1 1858 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice17 : pointSliceCheck 1 1858 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice18 : pointSliceCheck 1 1858 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice19 : pointSliceCheck 1 1858 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice20 : pointSliceCheck 1 1858 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice21 : pointSliceCheck 1 1858 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice22 : pointSliceCheck 1 1858 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice23 : pointSliceCheck 1 1858 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice24 : pointSliceCheck 1 1858 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice25 : pointSliceCheck 1 1858 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice26 : pointSliceCheck 1 1858 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice27 : pointSliceCheck 1 1858 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point62Slice28 : pointSliceCheck 1 1858 28 := by
  decide +kernel

public theorem point62 : residualCheck 62 := by
  apply ofPointSlices 1 1858
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
private theorem point63Slice0 : pointSliceCheck 0 1981 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice1 : pointSliceCheck 0 1981 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice2 : pointSliceCheck 0 1981 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice3 : pointSliceCheck 0 1981 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice4 : pointSliceCheck 0 1981 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice5 : pointSliceCheck 0 1981 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice6 : pointSliceCheck 0 1981 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice7 : pointSliceCheck 0 1981 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice8 : pointSliceCheck 0 1981 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice9 : pointSliceCheck 0 1981 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice10 : pointSliceCheck 0 1981 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice11 : pointSliceCheck 0 1981 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice12 : pointSliceCheck 0 1981 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice13 : pointSliceCheck 0 1981 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice14 : pointSliceCheck 0 1981 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice15 : pointSliceCheck 0 1981 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice16 : pointSliceCheck 0 1981 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice17 : pointSliceCheck 0 1981 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice18 : pointSliceCheck 0 1981 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice19 : pointSliceCheck 0 1981 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice20 : pointSliceCheck 0 1981 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice21 : pointSliceCheck 0 1981 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice22 : pointSliceCheck 0 1981 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice23 : pointSliceCheck 0 1981 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice24 : pointSliceCheck 0 1981 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice25 : pointSliceCheck 0 1981 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice26 : pointSliceCheck 0 1981 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice27 : pointSliceCheck 0 1981 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point63Slice28 : pointSliceCheck 0 1981 28 := by
  decide +kernel

public theorem point63 : residualCheck 63 := by
  apply ofPointSlices 0 1981
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
private theorem point64Slice0 : pointSliceCheck 0 1982 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice1 : pointSliceCheck 0 1982 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice2 : pointSliceCheck 0 1982 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice3 : pointSliceCheck 0 1982 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice4 : pointSliceCheck 0 1982 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice5 : pointSliceCheck 0 1982 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice6 : pointSliceCheck 0 1982 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice7 : pointSliceCheck 0 1982 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice8 : pointSliceCheck 0 1982 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice9 : pointSliceCheck 0 1982 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice10 : pointSliceCheck 0 1982 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice11 : pointSliceCheck 0 1982 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice12 : pointSliceCheck 0 1982 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice13 : pointSliceCheck 0 1982 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice14 : pointSliceCheck 0 1982 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice15 : pointSliceCheck 0 1982 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice16 : pointSliceCheck 0 1982 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice17 : pointSliceCheck 0 1982 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice18 : pointSliceCheck 0 1982 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice19 : pointSliceCheck 0 1982 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice20 : pointSliceCheck 0 1982 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice21 : pointSliceCheck 0 1982 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice22 : pointSliceCheck 0 1982 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice23 : pointSliceCheck 0 1982 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice24 : pointSliceCheck 0 1982 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice25 : pointSliceCheck 0 1982 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice26 : pointSliceCheck 0 1982 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice27 : pointSliceCheck 0 1982 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point64Slice28 : pointSliceCheck 0 1982 28 := by
  decide +kernel

public theorem point64 : residualCheck 64 := by
  apply ofPointSlices 0 1982
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

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
