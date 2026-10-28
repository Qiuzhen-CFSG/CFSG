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
private theorem point50Slice0 : pointSliceCheck 0 1840 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice1 : pointSliceCheck 0 1840 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice2 : pointSliceCheck 0 1840 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice3 : pointSliceCheck 0 1840 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice4 : pointSliceCheck 0 1840 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice5 : pointSliceCheck 0 1840 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice6 : pointSliceCheck 0 1840 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice7 : pointSliceCheck 0 1840 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice8 : pointSliceCheck 0 1840 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice9 : pointSliceCheck 0 1840 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice10 : pointSliceCheck 0 1840 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice11 : pointSliceCheck 0 1840 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice12 : pointSliceCheck 0 1840 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice13 : pointSliceCheck 0 1840 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice14 : pointSliceCheck 0 1840 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice15 : pointSliceCheck 0 1840 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice16 : pointSliceCheck 0 1840 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice17 : pointSliceCheck 0 1840 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice18 : pointSliceCheck 0 1840 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice19 : pointSliceCheck 0 1840 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice20 : pointSliceCheck 0 1840 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice21 : pointSliceCheck 0 1840 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice22 : pointSliceCheck 0 1840 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice23 : pointSliceCheck 0 1840 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice24 : pointSliceCheck 0 1840 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice25 : pointSliceCheck 0 1840 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice26 : pointSliceCheck 0 1840 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice27 : pointSliceCheck 0 1840 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice28 : pointSliceCheck 0 1840 28 := by
  decide +kernel

public theorem point50 : residualCheck 50 := by
  apply ofPointSlices 0 1840
  intro c
  fin_cases c
  · exact point50Slice0
  · exact point50Slice1
  · exact point50Slice2
  · exact point50Slice3
  · exact point50Slice4
  · exact point50Slice5
  · exact point50Slice6
  · exact point50Slice7
  · exact point50Slice8
  · exact point50Slice9
  · exact point50Slice10
  · exact point50Slice11
  · exact point50Slice12
  · exact point50Slice13
  · exact point50Slice14
  · exact point50Slice15
  · exact point50Slice16
  · exact point50Slice17
  · exact point50Slice18
  · exact point50Slice19
  · exact point50Slice20
  · exact point50Slice21
  · exact point50Slice22
  · exact point50Slice23
  · exact point50Slice24
  · exact point50Slice25
  · exact point50Slice26
  · exact point50Slice27
  · exact point50Slice28

set_option maxHeartbeats 1600000 in
private theorem point51Slice0 : pointSliceCheck 0 1843 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice1 : pointSliceCheck 0 1843 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice2 : pointSliceCheck 0 1843 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice3 : pointSliceCheck 0 1843 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice4 : pointSliceCheck 0 1843 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice5 : pointSliceCheck 0 1843 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice6 : pointSliceCheck 0 1843 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice7 : pointSliceCheck 0 1843 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice8 : pointSliceCheck 0 1843 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice9 : pointSliceCheck 0 1843 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice10 : pointSliceCheck 0 1843 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice11 : pointSliceCheck 0 1843 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice12 : pointSliceCheck 0 1843 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice13 : pointSliceCheck 0 1843 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice14 : pointSliceCheck 0 1843 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice15 : pointSliceCheck 0 1843 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice16 : pointSliceCheck 0 1843 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice17 : pointSliceCheck 0 1843 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice18 : pointSliceCheck 0 1843 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice19 : pointSliceCheck 0 1843 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice20 : pointSliceCheck 0 1843 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice21 : pointSliceCheck 0 1843 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice22 : pointSliceCheck 0 1843 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice23 : pointSliceCheck 0 1843 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice24 : pointSliceCheck 0 1843 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice25 : pointSliceCheck 0 1843 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice26 : pointSliceCheck 0 1843 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice27 : pointSliceCheck 0 1843 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice28 : pointSliceCheck 0 1843 28 := by
  decide +kernel

public theorem point51 : residualCheck 51 := by
  apply ofPointSlices 0 1843
  intro c
  fin_cases c
  · exact point51Slice0
  · exact point51Slice1
  · exact point51Slice2
  · exact point51Slice3
  · exact point51Slice4
  · exact point51Slice5
  · exact point51Slice6
  · exact point51Slice7
  · exact point51Slice8
  · exact point51Slice9
  · exact point51Slice10
  · exact point51Slice11
  · exact point51Slice12
  · exact point51Slice13
  · exact point51Slice14
  · exact point51Slice15
  · exact point51Slice16
  · exact point51Slice17
  · exact point51Slice18
  · exact point51Slice19
  · exact point51Slice20
  · exact point51Slice21
  · exact point51Slice22
  · exact point51Slice23
  · exact point51Slice24
  · exact point51Slice25
  · exact point51Slice26
  · exact point51Slice27
  · exact point51Slice28

set_option maxHeartbeats 1600000 in
private theorem point52Slice0 : pointSliceCheck 0 1852 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice1 : pointSliceCheck 0 1852 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice2 : pointSliceCheck 0 1852 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice3 : pointSliceCheck 0 1852 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice4 : pointSliceCheck 0 1852 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice5 : pointSliceCheck 0 1852 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice6 : pointSliceCheck 0 1852 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice7 : pointSliceCheck 0 1852 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice8 : pointSliceCheck 0 1852 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice9 : pointSliceCheck 0 1852 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice10 : pointSliceCheck 0 1852 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice11 : pointSliceCheck 0 1852 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice12 : pointSliceCheck 0 1852 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice13 : pointSliceCheck 0 1852 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice14 : pointSliceCheck 0 1852 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice15 : pointSliceCheck 0 1852 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice16 : pointSliceCheck 0 1852 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice17 : pointSliceCheck 0 1852 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice18 : pointSliceCheck 0 1852 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice19 : pointSliceCheck 0 1852 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice20 : pointSliceCheck 0 1852 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice21 : pointSliceCheck 0 1852 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice22 : pointSliceCheck 0 1852 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice23 : pointSliceCheck 0 1852 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice24 : pointSliceCheck 0 1852 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice25 : pointSliceCheck 0 1852 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice26 : pointSliceCheck 0 1852 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice27 : pointSliceCheck 0 1852 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice28 : pointSliceCheck 0 1852 28 := by
  decide +kernel

public theorem point52 : residualCheck 52 := by
  apply ofPointSlices 0 1852
  intro c
  fin_cases c
  · exact point52Slice0
  · exact point52Slice1
  · exact point52Slice2
  · exact point52Slice3
  · exact point52Slice4
  · exact point52Slice5
  · exact point52Slice6
  · exact point52Slice7
  · exact point52Slice8
  · exact point52Slice9
  · exact point52Slice10
  · exact point52Slice11
  · exact point52Slice12
  · exact point52Slice13
  · exact point52Slice14
  · exact point52Slice15
  · exact point52Slice16
  · exact point52Slice17
  · exact point52Slice18
  · exact point52Slice19
  · exact point52Slice20
  · exact point52Slice21
  · exact point52Slice22
  · exact point52Slice23
  · exact point52Slice24
  · exact point52Slice25
  · exact point52Slice26
  · exact point52Slice27
  · exact point52Slice28

set_option maxHeartbeats 1600000 in
private theorem point53Slice0 : pointSliceCheck 0 1853 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice1 : pointSliceCheck 0 1853 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice2 : pointSliceCheck 0 1853 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice3 : pointSliceCheck 0 1853 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice4 : pointSliceCheck 0 1853 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice5 : pointSliceCheck 0 1853 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice6 : pointSliceCheck 0 1853 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice7 : pointSliceCheck 0 1853 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice8 : pointSliceCheck 0 1853 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice9 : pointSliceCheck 0 1853 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice10 : pointSliceCheck 0 1853 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice11 : pointSliceCheck 0 1853 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice12 : pointSliceCheck 0 1853 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice13 : pointSliceCheck 0 1853 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice14 : pointSliceCheck 0 1853 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice15 : pointSliceCheck 0 1853 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice16 : pointSliceCheck 0 1853 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice17 : pointSliceCheck 0 1853 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice18 : pointSliceCheck 0 1853 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice19 : pointSliceCheck 0 1853 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice20 : pointSliceCheck 0 1853 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice21 : pointSliceCheck 0 1853 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice22 : pointSliceCheck 0 1853 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice23 : pointSliceCheck 0 1853 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice24 : pointSliceCheck 0 1853 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice25 : pointSliceCheck 0 1853 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice26 : pointSliceCheck 0 1853 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice27 : pointSliceCheck 0 1853 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice28 : pointSliceCheck 0 1853 28 := by
  decide +kernel

public theorem point53 : residualCheck 53 := by
  apply ofPointSlices 0 1853
  intro c
  fin_cases c
  · exact point53Slice0
  · exact point53Slice1
  · exact point53Slice2
  · exact point53Slice3
  · exact point53Slice4
  · exact point53Slice5
  · exact point53Slice6
  · exact point53Slice7
  · exact point53Slice8
  · exact point53Slice9
  · exact point53Slice10
  · exact point53Slice11
  · exact point53Slice12
  · exact point53Slice13
  · exact point53Slice14
  · exact point53Slice15
  · exact point53Slice16
  · exact point53Slice17
  · exact point53Slice18
  · exact point53Slice19
  · exact point53Slice20
  · exact point53Slice21
  · exact point53Slice22
  · exact point53Slice23
  · exact point53Slice24
  · exact point53Slice25
  · exact point53Slice26
  · exact point53Slice27
  · exact point53Slice28

set_option maxHeartbeats 1600000 in
private theorem point54Slice0 : pointSliceCheck 0 1857 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice1 : pointSliceCheck 0 1857 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice2 : pointSliceCheck 0 1857 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice3 : pointSliceCheck 0 1857 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice4 : pointSliceCheck 0 1857 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice5 : pointSliceCheck 0 1857 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice6 : pointSliceCheck 0 1857 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice7 : pointSliceCheck 0 1857 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice8 : pointSliceCheck 0 1857 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice9 : pointSliceCheck 0 1857 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice10 : pointSliceCheck 0 1857 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice11 : pointSliceCheck 0 1857 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice12 : pointSliceCheck 0 1857 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice13 : pointSliceCheck 0 1857 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice14 : pointSliceCheck 0 1857 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice15 : pointSliceCheck 0 1857 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice16 : pointSliceCheck 0 1857 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice17 : pointSliceCheck 0 1857 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice18 : pointSliceCheck 0 1857 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice19 : pointSliceCheck 0 1857 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice20 : pointSliceCheck 0 1857 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice21 : pointSliceCheck 0 1857 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice22 : pointSliceCheck 0 1857 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice23 : pointSliceCheck 0 1857 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice24 : pointSliceCheck 0 1857 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice25 : pointSliceCheck 0 1857 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice26 : pointSliceCheck 0 1857 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice27 : pointSliceCheck 0 1857 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice28 : pointSliceCheck 0 1857 28 := by
  decide +kernel

public theorem point54 : residualCheck 54 := by
  apply ofPointSlices 0 1857
  intro c
  fin_cases c
  · exact point54Slice0
  · exact point54Slice1
  · exact point54Slice2
  · exact point54Slice3
  · exact point54Slice4
  · exact point54Slice5
  · exact point54Slice6
  · exact point54Slice7
  · exact point54Slice8
  · exact point54Slice9
  · exact point54Slice10
  · exact point54Slice11
  · exact point54Slice12
  · exact point54Slice13
  · exact point54Slice14
  · exact point54Slice15
  · exact point54Slice16
  · exact point54Slice17
  · exact point54Slice18
  · exact point54Slice19
  · exact point54Slice20
  · exact point54Slice21
  · exact point54Slice22
  · exact point54Slice23
  · exact point54Slice24
  · exact point54Slice25
  · exact point54Slice26
  · exact point54Slice27
  · exact point54Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
