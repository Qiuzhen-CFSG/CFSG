module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 55–59

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point55Slice0 : pointSliceCheck 1 1839 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice1 : pointSliceCheck 1 1839 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice2 : pointSliceCheck 1 1839 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice3 : pointSliceCheck 1 1839 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice4 : pointSliceCheck 1 1839 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice5 : pointSliceCheck 1 1839 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice6 : pointSliceCheck 1 1839 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice7 : pointSliceCheck 1 1839 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice8 : pointSliceCheck 1 1839 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice9 : pointSliceCheck 1 1839 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice10 : pointSliceCheck 1 1839 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice11 : pointSliceCheck 1 1839 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice12 : pointSliceCheck 1 1839 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice13 : pointSliceCheck 1 1839 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice14 : pointSliceCheck 1 1839 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice15 : pointSliceCheck 1 1839 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice16 : pointSliceCheck 1 1839 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice17 : pointSliceCheck 1 1839 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice18 : pointSliceCheck 1 1839 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice19 : pointSliceCheck 1 1839 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice20 : pointSliceCheck 1 1839 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice21 : pointSliceCheck 1 1839 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice22 : pointSliceCheck 1 1839 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice23 : pointSliceCheck 1 1839 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice24 : pointSliceCheck 1 1839 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice25 : pointSliceCheck 1 1839 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice26 : pointSliceCheck 1 1839 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice27 : pointSliceCheck 1 1839 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice28 : pointSliceCheck 1 1839 28 := by
  decide +kernel

public theorem point55 : residualCheck 55 := by
  apply ofPointSlices 1 1839
  intro c
  fin_cases c
  · exact point55Slice0
  · exact point55Slice1
  · exact point55Slice2
  · exact point55Slice3
  · exact point55Slice4
  · exact point55Slice5
  · exact point55Slice6
  · exact point55Slice7
  · exact point55Slice8
  · exact point55Slice9
  · exact point55Slice10
  · exact point55Slice11
  · exact point55Slice12
  · exact point55Slice13
  · exact point55Slice14
  · exact point55Slice15
  · exact point55Slice16
  · exact point55Slice17
  · exact point55Slice18
  · exact point55Slice19
  · exact point55Slice20
  · exact point55Slice21
  · exact point55Slice22
  · exact point55Slice23
  · exact point55Slice24
  · exact point55Slice25
  · exact point55Slice26
  · exact point55Slice27
  · exact point55Slice28

set_option maxHeartbeats 1600000 in
private theorem point56Slice0 : pointSliceCheck 0 1962 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice1 : pointSliceCheck 0 1962 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice2 : pointSliceCheck 0 1962 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice3 : pointSliceCheck 0 1962 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice4 : pointSliceCheck 0 1962 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice5 : pointSliceCheck 0 1962 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice6 : pointSliceCheck 0 1962 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice7 : pointSliceCheck 0 1962 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice8 : pointSliceCheck 0 1962 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice9 : pointSliceCheck 0 1962 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice10 : pointSliceCheck 0 1962 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice11 : pointSliceCheck 0 1962 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice12 : pointSliceCheck 0 1962 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice13 : pointSliceCheck 0 1962 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice14 : pointSliceCheck 0 1962 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice15 : pointSliceCheck 0 1962 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice16 : pointSliceCheck 0 1962 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice17 : pointSliceCheck 0 1962 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice18 : pointSliceCheck 0 1962 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice19 : pointSliceCheck 0 1962 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice20 : pointSliceCheck 0 1962 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice21 : pointSliceCheck 0 1962 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice22 : pointSliceCheck 0 1962 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice23 : pointSliceCheck 0 1962 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice24 : pointSliceCheck 0 1962 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice25 : pointSliceCheck 0 1962 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice26 : pointSliceCheck 0 1962 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice27 : pointSliceCheck 0 1962 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice28 : pointSliceCheck 0 1962 28 := by
  decide +kernel

public theorem point56 : residualCheck 56 := by
  apply ofPointSlices 0 1962
  intro c
  fin_cases c
  · exact point56Slice0
  · exact point56Slice1
  · exact point56Slice2
  · exact point56Slice3
  · exact point56Slice4
  · exact point56Slice5
  · exact point56Slice6
  · exact point56Slice7
  · exact point56Slice8
  · exact point56Slice9
  · exact point56Slice10
  · exact point56Slice11
  · exact point56Slice12
  · exact point56Slice13
  · exact point56Slice14
  · exact point56Slice15
  · exact point56Slice16
  · exact point56Slice17
  · exact point56Slice18
  · exact point56Slice19
  · exact point56Slice20
  · exact point56Slice21
  · exact point56Slice22
  · exact point56Slice23
  · exact point56Slice24
  · exact point56Slice25
  · exact point56Slice26
  · exact point56Slice27
  · exact point56Slice28

set_option maxHeartbeats 1600000 in
private theorem point57Slice0 : pointSliceCheck 0 1964 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice1 : pointSliceCheck 0 1964 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice2 : pointSliceCheck 0 1964 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice3 : pointSliceCheck 0 1964 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice4 : pointSliceCheck 0 1964 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice5 : pointSliceCheck 0 1964 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice6 : pointSliceCheck 0 1964 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice7 : pointSliceCheck 0 1964 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice8 : pointSliceCheck 0 1964 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice9 : pointSliceCheck 0 1964 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice10 : pointSliceCheck 0 1964 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice11 : pointSliceCheck 0 1964 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice12 : pointSliceCheck 0 1964 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice13 : pointSliceCheck 0 1964 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice14 : pointSliceCheck 0 1964 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice15 : pointSliceCheck 0 1964 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice16 : pointSliceCheck 0 1964 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice17 : pointSliceCheck 0 1964 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice18 : pointSliceCheck 0 1964 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice19 : pointSliceCheck 0 1964 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice20 : pointSliceCheck 0 1964 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice21 : pointSliceCheck 0 1964 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice22 : pointSliceCheck 0 1964 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice23 : pointSliceCheck 0 1964 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice24 : pointSliceCheck 0 1964 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice25 : pointSliceCheck 0 1964 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice26 : pointSliceCheck 0 1964 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice27 : pointSliceCheck 0 1964 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice28 : pointSliceCheck 0 1964 28 := by
  decide +kernel

public theorem point57 : residualCheck 57 := by
  apply ofPointSlices 0 1964
  intro c
  fin_cases c
  · exact point57Slice0
  · exact point57Slice1
  · exact point57Slice2
  · exact point57Slice3
  · exact point57Slice4
  · exact point57Slice5
  · exact point57Slice6
  · exact point57Slice7
  · exact point57Slice8
  · exact point57Slice9
  · exact point57Slice10
  · exact point57Slice11
  · exact point57Slice12
  · exact point57Slice13
  · exact point57Slice14
  · exact point57Slice15
  · exact point57Slice16
  · exact point57Slice17
  · exact point57Slice18
  · exact point57Slice19
  · exact point57Slice20
  · exact point57Slice21
  · exact point57Slice22
  · exact point57Slice23
  · exact point57Slice24
  · exact point57Slice25
  · exact point57Slice26
  · exact point57Slice27
  · exact point57Slice28

set_option maxHeartbeats 1600000 in
private theorem point58Slice0 : pointSliceCheck 0 1967 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice1 : pointSliceCheck 0 1967 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice2 : pointSliceCheck 0 1967 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice3 : pointSliceCheck 0 1967 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice4 : pointSliceCheck 0 1967 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice5 : pointSliceCheck 0 1967 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice6 : pointSliceCheck 0 1967 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice7 : pointSliceCheck 0 1967 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice8 : pointSliceCheck 0 1967 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice9 : pointSliceCheck 0 1967 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice10 : pointSliceCheck 0 1967 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice11 : pointSliceCheck 0 1967 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice12 : pointSliceCheck 0 1967 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice13 : pointSliceCheck 0 1967 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice14 : pointSliceCheck 0 1967 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice15 : pointSliceCheck 0 1967 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice16 : pointSliceCheck 0 1967 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice17 : pointSliceCheck 0 1967 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice18 : pointSliceCheck 0 1967 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice19 : pointSliceCheck 0 1967 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice20 : pointSliceCheck 0 1967 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice21 : pointSliceCheck 0 1967 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice22 : pointSliceCheck 0 1967 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice23 : pointSliceCheck 0 1967 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice24 : pointSliceCheck 0 1967 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice25 : pointSliceCheck 0 1967 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice26 : pointSliceCheck 0 1967 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice27 : pointSliceCheck 0 1967 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice28 : pointSliceCheck 0 1967 28 := by
  decide +kernel

public theorem point58 : residualCheck 58 := by
  apply ofPointSlices 0 1967
  intro c
  fin_cases c
  · exact point58Slice0
  · exact point58Slice1
  · exact point58Slice2
  · exact point58Slice3
  · exact point58Slice4
  · exact point58Slice5
  · exact point58Slice6
  · exact point58Slice7
  · exact point58Slice8
  · exact point58Slice9
  · exact point58Slice10
  · exact point58Slice11
  · exact point58Slice12
  · exact point58Slice13
  · exact point58Slice14
  · exact point58Slice15
  · exact point58Slice16
  · exact point58Slice17
  · exact point58Slice18
  · exact point58Slice19
  · exact point58Slice20
  · exact point58Slice21
  · exact point58Slice22
  · exact point58Slice23
  · exact point58Slice24
  · exact point58Slice25
  · exact point58Slice26
  · exact point58Slice27
  · exact point58Slice28

set_option maxHeartbeats 1600000 in
private theorem point59Slice0 : pointSliceCheck 0 1974 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice1 : pointSliceCheck 0 1974 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice2 : pointSliceCheck 0 1974 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice3 : pointSliceCheck 0 1974 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice4 : pointSliceCheck 0 1974 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice5 : pointSliceCheck 0 1974 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice6 : pointSliceCheck 0 1974 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice7 : pointSliceCheck 0 1974 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice8 : pointSliceCheck 0 1974 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice9 : pointSliceCheck 0 1974 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice10 : pointSliceCheck 0 1974 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice11 : pointSliceCheck 0 1974 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice12 : pointSliceCheck 0 1974 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice13 : pointSliceCheck 0 1974 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice14 : pointSliceCheck 0 1974 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice15 : pointSliceCheck 0 1974 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice16 : pointSliceCheck 0 1974 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice17 : pointSliceCheck 0 1974 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice18 : pointSliceCheck 0 1974 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice19 : pointSliceCheck 0 1974 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice20 : pointSliceCheck 0 1974 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice21 : pointSliceCheck 0 1974 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice22 : pointSliceCheck 0 1974 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice23 : pointSliceCheck 0 1974 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice24 : pointSliceCheck 0 1974 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice25 : pointSliceCheck 0 1974 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice26 : pointSliceCheck 0 1974 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice27 : pointSliceCheck 0 1974 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice28 : pointSliceCheck 0 1974 28 := by
  decide +kernel

public theorem point59 : residualCheck 59 := by
  apply ofPointSlices 0 1974
  intro c
  fin_cases c
  · exact point59Slice0
  · exact point59Slice1
  · exact point59Slice2
  · exact point59Slice3
  · exact point59Slice4
  · exact point59Slice5
  · exact point59Slice6
  · exact point59Slice7
  · exact point59Slice8
  · exact point59Slice9
  · exact point59Slice10
  · exact point59Slice11
  · exact point59Slice12
  · exact point59Slice13
  · exact point59Slice14
  · exact point59Slice15
  · exact point59Slice16
  · exact point59Slice17
  · exact point59Slice18
  · exact point59Slice19
  · exact point59Slice20
  · exact point59Slice21
  · exact point59Slice22
  · exact point59Slice23
  · exact point59Slice24
  · exact point59Slice25
  · exact point59Slice26
  · exact point59Slice27
  · exact point59Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
