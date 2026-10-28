module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 50–54

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point50Slice0 : pointSliceCheck 1 1690 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice1 : pointSliceCheck 1 1690 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice2 : pointSliceCheck 1 1690 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice3 : pointSliceCheck 1 1690 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice4 : pointSliceCheck 1 1690 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice5 : pointSliceCheck 1 1690 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice6 : pointSliceCheck 1 1690 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice7 : pointSliceCheck 1 1690 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice8 : pointSliceCheck 1 1690 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice9 : pointSliceCheck 1 1690 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice10 : pointSliceCheck 1 1690 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice11 : pointSliceCheck 1 1690 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice12 : pointSliceCheck 1 1690 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice13 : pointSliceCheck 1 1690 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice14 : pointSliceCheck 1 1690 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice15 : pointSliceCheck 1 1690 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice16 : pointSliceCheck 1 1690 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice17 : pointSliceCheck 1 1690 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice18 : pointSliceCheck 1 1690 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice19 : pointSliceCheck 1 1690 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice20 : pointSliceCheck 1 1690 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice21 : pointSliceCheck 1 1690 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice22 : pointSliceCheck 1 1690 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice23 : pointSliceCheck 1 1690 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice24 : pointSliceCheck 1 1690 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice25 : pointSliceCheck 1 1690 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice26 : pointSliceCheck 1 1690 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice27 : pointSliceCheck 1 1690 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point50Slice28 : pointSliceCheck 1 1690 28 := by
  decide +kernel

public theorem point50 : residualCheck 50 := by
  apply ofPointSlices 1 1690
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
private theorem point51Slice0 : pointSliceCheck 1 1692 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice1 : pointSliceCheck 1 1692 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice2 : pointSliceCheck 1 1692 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice3 : pointSliceCheck 1 1692 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice4 : pointSliceCheck 1 1692 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice5 : pointSliceCheck 1 1692 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice6 : pointSliceCheck 1 1692 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice7 : pointSliceCheck 1 1692 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice8 : pointSliceCheck 1 1692 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice9 : pointSliceCheck 1 1692 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice10 : pointSliceCheck 1 1692 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice11 : pointSliceCheck 1 1692 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice12 : pointSliceCheck 1 1692 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice13 : pointSliceCheck 1 1692 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice14 : pointSliceCheck 1 1692 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice15 : pointSliceCheck 1 1692 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice16 : pointSliceCheck 1 1692 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice17 : pointSliceCheck 1 1692 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice18 : pointSliceCheck 1 1692 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice19 : pointSliceCheck 1 1692 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice20 : pointSliceCheck 1 1692 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice21 : pointSliceCheck 1 1692 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice22 : pointSliceCheck 1 1692 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice23 : pointSliceCheck 1 1692 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice24 : pointSliceCheck 1 1692 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice25 : pointSliceCheck 1 1692 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice26 : pointSliceCheck 1 1692 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice27 : pointSliceCheck 1 1692 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point51Slice28 : pointSliceCheck 1 1692 28 := by
  decide +kernel

public theorem point51 : residualCheck 51 := by
  apply ofPointSlices 1 1692
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
private theorem point52Slice0 : pointSliceCheck 0 1830 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice1 : pointSliceCheck 0 1830 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice2 : pointSliceCheck 0 1830 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice3 : pointSliceCheck 0 1830 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice4 : pointSliceCheck 0 1830 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice5 : pointSliceCheck 0 1830 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice6 : pointSliceCheck 0 1830 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice7 : pointSliceCheck 0 1830 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice8 : pointSliceCheck 0 1830 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice9 : pointSliceCheck 0 1830 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice10 : pointSliceCheck 0 1830 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice11 : pointSliceCheck 0 1830 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice12 : pointSliceCheck 0 1830 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice13 : pointSliceCheck 0 1830 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice14 : pointSliceCheck 0 1830 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice15 : pointSliceCheck 0 1830 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice16 : pointSliceCheck 0 1830 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice17 : pointSliceCheck 0 1830 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice18 : pointSliceCheck 0 1830 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice19 : pointSliceCheck 0 1830 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice20 : pointSliceCheck 0 1830 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice21 : pointSliceCheck 0 1830 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice22 : pointSliceCheck 0 1830 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice23 : pointSliceCheck 0 1830 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice24 : pointSliceCheck 0 1830 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice25 : pointSliceCheck 0 1830 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice26 : pointSliceCheck 0 1830 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice27 : pointSliceCheck 0 1830 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point52Slice28 : pointSliceCheck 0 1830 28 := by
  decide +kernel

public theorem point52 : residualCheck 52 := by
  apply ofPointSlices 0 1830
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
private theorem point53Slice0 : pointSliceCheck 0 1838 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice1 : pointSliceCheck 0 1838 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice2 : pointSliceCheck 0 1838 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice3 : pointSliceCheck 0 1838 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice4 : pointSliceCheck 0 1838 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice5 : pointSliceCheck 0 1838 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice6 : pointSliceCheck 0 1838 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice7 : pointSliceCheck 0 1838 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice8 : pointSliceCheck 0 1838 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice9 : pointSliceCheck 0 1838 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice10 : pointSliceCheck 0 1838 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice11 : pointSliceCheck 0 1838 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice12 : pointSliceCheck 0 1838 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice13 : pointSliceCheck 0 1838 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice14 : pointSliceCheck 0 1838 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice15 : pointSliceCheck 0 1838 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice16 : pointSliceCheck 0 1838 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice17 : pointSliceCheck 0 1838 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice18 : pointSliceCheck 0 1838 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice19 : pointSliceCheck 0 1838 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice20 : pointSliceCheck 0 1838 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice21 : pointSliceCheck 0 1838 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice22 : pointSliceCheck 0 1838 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice23 : pointSliceCheck 0 1838 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice24 : pointSliceCheck 0 1838 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice25 : pointSliceCheck 0 1838 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice26 : pointSliceCheck 0 1838 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice27 : pointSliceCheck 0 1838 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point53Slice28 : pointSliceCheck 0 1838 28 := by
  decide +kernel

public theorem point53 : residualCheck 53 := by
  apply ofPointSlices 0 1838
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
private theorem point54Slice0 : pointSliceCheck 1 1837 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice1 : pointSliceCheck 1 1837 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice2 : pointSliceCheck 1 1837 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice3 : pointSliceCheck 1 1837 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice4 : pointSliceCheck 1 1837 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice5 : pointSliceCheck 1 1837 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice6 : pointSliceCheck 1 1837 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice7 : pointSliceCheck 1 1837 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice8 : pointSliceCheck 1 1837 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice9 : pointSliceCheck 1 1837 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice10 : pointSliceCheck 1 1837 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice11 : pointSliceCheck 1 1837 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice12 : pointSliceCheck 1 1837 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice13 : pointSliceCheck 1 1837 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice14 : pointSliceCheck 1 1837 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice15 : pointSliceCheck 1 1837 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice16 : pointSliceCheck 1 1837 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice17 : pointSliceCheck 1 1837 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice18 : pointSliceCheck 1 1837 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice19 : pointSliceCheck 1 1837 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice20 : pointSliceCheck 1 1837 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice21 : pointSliceCheck 1 1837 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice22 : pointSliceCheck 1 1837 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice23 : pointSliceCheck 1 1837 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice24 : pointSliceCheck 1 1837 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice25 : pointSliceCheck 1 1837 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice26 : pointSliceCheck 1 1837 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice27 : pointSliceCheck 1 1837 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point54Slice28 : pointSliceCheck 1 1837 28 := by
  decide +kernel

public theorem point54 : residualCheck 54 := by
  apply ofPointSlices 1 1837
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

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
