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
private theorem point55Slice0 : pointSliceCheck 0 1858 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice1 : pointSliceCheck 0 1858 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice2 : pointSliceCheck 0 1858 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice3 : pointSliceCheck 0 1858 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice4 : pointSliceCheck 0 1858 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice5 : pointSliceCheck 0 1858 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice6 : pointSliceCheck 0 1858 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice7 : pointSliceCheck 0 1858 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice8 : pointSliceCheck 0 1858 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice9 : pointSliceCheck 0 1858 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice10 : pointSliceCheck 0 1858 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice11 : pointSliceCheck 0 1858 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice12 : pointSliceCheck 0 1858 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice13 : pointSliceCheck 0 1858 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice14 : pointSliceCheck 0 1858 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice15 : pointSliceCheck 0 1858 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice16 : pointSliceCheck 0 1858 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice17 : pointSliceCheck 0 1858 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice18 : pointSliceCheck 0 1858 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice19 : pointSliceCheck 0 1858 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice20 : pointSliceCheck 0 1858 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice21 : pointSliceCheck 0 1858 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice22 : pointSliceCheck 0 1858 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice23 : pointSliceCheck 0 1858 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice24 : pointSliceCheck 0 1858 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice25 : pointSliceCheck 0 1858 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice26 : pointSliceCheck 0 1858 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice27 : pointSliceCheck 0 1858 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point55Slice28 : pointSliceCheck 0 1858 28 := by
  decide +kernel

public theorem point55 : residualCheck 55 := by
  apply ofPointSlices 0 1858
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
private theorem point56Slice0 : pointSliceCheck 0 1859 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice1 : pointSliceCheck 0 1859 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice2 : pointSliceCheck 0 1859 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice3 : pointSliceCheck 0 1859 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice4 : pointSliceCheck 0 1859 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice5 : pointSliceCheck 0 1859 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice6 : pointSliceCheck 0 1859 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice7 : pointSliceCheck 0 1859 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice8 : pointSliceCheck 0 1859 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice9 : pointSliceCheck 0 1859 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice10 : pointSliceCheck 0 1859 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice11 : pointSliceCheck 0 1859 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice12 : pointSliceCheck 0 1859 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice13 : pointSliceCheck 0 1859 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice14 : pointSliceCheck 0 1859 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice15 : pointSliceCheck 0 1859 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice16 : pointSliceCheck 0 1859 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice17 : pointSliceCheck 0 1859 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice18 : pointSliceCheck 0 1859 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice19 : pointSliceCheck 0 1859 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice20 : pointSliceCheck 0 1859 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice21 : pointSliceCheck 0 1859 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice22 : pointSliceCheck 0 1859 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice23 : pointSliceCheck 0 1859 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice24 : pointSliceCheck 0 1859 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice25 : pointSliceCheck 0 1859 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice26 : pointSliceCheck 0 1859 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice27 : pointSliceCheck 0 1859 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point56Slice28 : pointSliceCheck 0 1859 28 := by
  decide +kernel

public theorem point56 : residualCheck 56 := by
  apply ofPointSlices 0 1859
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
private theorem point57Slice0 : pointSliceCheck 1 1841 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice1 : pointSliceCheck 1 1841 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice2 : pointSliceCheck 1 1841 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice3 : pointSliceCheck 1 1841 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice4 : pointSliceCheck 1 1841 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice5 : pointSliceCheck 1 1841 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice6 : pointSliceCheck 1 1841 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice7 : pointSliceCheck 1 1841 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice8 : pointSliceCheck 1 1841 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice9 : pointSliceCheck 1 1841 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice10 : pointSliceCheck 1 1841 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice11 : pointSliceCheck 1 1841 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice12 : pointSliceCheck 1 1841 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice13 : pointSliceCheck 1 1841 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice14 : pointSliceCheck 1 1841 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice15 : pointSliceCheck 1 1841 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice16 : pointSliceCheck 1 1841 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice17 : pointSliceCheck 1 1841 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice18 : pointSliceCheck 1 1841 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice19 : pointSliceCheck 1 1841 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice20 : pointSliceCheck 1 1841 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice21 : pointSliceCheck 1 1841 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice22 : pointSliceCheck 1 1841 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice23 : pointSliceCheck 1 1841 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice24 : pointSliceCheck 1 1841 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice25 : pointSliceCheck 1 1841 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice26 : pointSliceCheck 1 1841 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice27 : pointSliceCheck 1 1841 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point57Slice28 : pointSliceCheck 1 1841 28 := by
  decide +kernel

public theorem point57 : residualCheck 57 := by
  apply ofPointSlices 1 1841
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
private theorem point58Slice0 : pointSliceCheck 1 1847 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice1 : pointSliceCheck 1 1847 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice2 : pointSliceCheck 1 1847 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice3 : pointSliceCheck 1 1847 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice4 : pointSliceCheck 1 1847 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice5 : pointSliceCheck 1 1847 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice6 : pointSliceCheck 1 1847 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice7 : pointSliceCheck 1 1847 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice8 : pointSliceCheck 1 1847 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice9 : pointSliceCheck 1 1847 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice10 : pointSliceCheck 1 1847 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice11 : pointSliceCheck 1 1847 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice12 : pointSliceCheck 1 1847 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice13 : pointSliceCheck 1 1847 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice14 : pointSliceCheck 1 1847 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice15 : pointSliceCheck 1 1847 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice16 : pointSliceCheck 1 1847 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice17 : pointSliceCheck 1 1847 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice18 : pointSliceCheck 1 1847 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice19 : pointSliceCheck 1 1847 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice20 : pointSliceCheck 1 1847 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice21 : pointSliceCheck 1 1847 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice22 : pointSliceCheck 1 1847 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice23 : pointSliceCheck 1 1847 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice24 : pointSliceCheck 1 1847 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice25 : pointSliceCheck 1 1847 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice26 : pointSliceCheck 1 1847 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice27 : pointSliceCheck 1 1847 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point58Slice28 : pointSliceCheck 1 1847 28 := by
  decide +kernel

public theorem point58 : residualCheck 58 := by
  apply ofPointSlices 1 1847
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
private theorem point59Slice0 : pointSliceCheck 1 1849 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice1 : pointSliceCheck 1 1849 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice2 : pointSliceCheck 1 1849 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice3 : pointSliceCheck 1 1849 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice4 : pointSliceCheck 1 1849 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice5 : pointSliceCheck 1 1849 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice6 : pointSliceCheck 1 1849 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice7 : pointSliceCheck 1 1849 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice8 : pointSliceCheck 1 1849 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice9 : pointSliceCheck 1 1849 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice10 : pointSliceCheck 1 1849 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice11 : pointSliceCheck 1 1849 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice12 : pointSliceCheck 1 1849 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice13 : pointSliceCheck 1 1849 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice14 : pointSliceCheck 1 1849 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice15 : pointSliceCheck 1 1849 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice16 : pointSliceCheck 1 1849 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice17 : pointSliceCheck 1 1849 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice18 : pointSliceCheck 1 1849 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice19 : pointSliceCheck 1 1849 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice20 : pointSliceCheck 1 1849 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice21 : pointSliceCheck 1 1849 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice22 : pointSliceCheck 1 1849 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice23 : pointSliceCheck 1 1849 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice24 : pointSliceCheck 1 1849 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice25 : pointSliceCheck 1 1849 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice26 : pointSliceCheck 1 1849 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice27 : pointSliceCheck 1 1849 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point59Slice28 : pointSliceCheck 1 1849 28 := by
  decide +kernel

public theorem point59 : residualCheck 59 := by
  apply ofPointSlices 1 1849
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

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
