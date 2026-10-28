module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 40–44

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point40Slice0 : pointSliceCheck 1 1550 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice1 : pointSliceCheck 1 1550 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice2 : pointSliceCheck 1 1550 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice3 : pointSliceCheck 1 1550 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice4 : pointSliceCheck 1 1550 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice5 : pointSliceCheck 1 1550 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice6 : pointSliceCheck 1 1550 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice7 : pointSliceCheck 1 1550 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice8 : pointSliceCheck 1 1550 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice9 : pointSliceCheck 1 1550 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice10 : pointSliceCheck 1 1550 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice11 : pointSliceCheck 1 1550 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice12 : pointSliceCheck 1 1550 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice13 : pointSliceCheck 1 1550 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice14 : pointSliceCheck 1 1550 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice15 : pointSliceCheck 1 1550 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice16 : pointSliceCheck 1 1550 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice17 : pointSliceCheck 1 1550 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice18 : pointSliceCheck 1 1550 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice19 : pointSliceCheck 1 1550 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice20 : pointSliceCheck 1 1550 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice21 : pointSliceCheck 1 1550 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice22 : pointSliceCheck 1 1550 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice23 : pointSliceCheck 1 1550 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice24 : pointSliceCheck 1 1550 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice25 : pointSliceCheck 1 1550 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice26 : pointSliceCheck 1 1550 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice27 : pointSliceCheck 1 1550 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice28 : pointSliceCheck 1 1550 28 := by
  decide +kernel

public theorem point40 : residualCheck 40 := by
  apply ofPointSlices 1 1550
  intro c
  fin_cases c
  · exact point40Slice0
  · exact point40Slice1
  · exact point40Slice2
  · exact point40Slice3
  · exact point40Slice4
  · exact point40Slice5
  · exact point40Slice6
  · exact point40Slice7
  · exact point40Slice8
  · exact point40Slice9
  · exact point40Slice10
  · exact point40Slice11
  · exact point40Slice12
  · exact point40Slice13
  · exact point40Slice14
  · exact point40Slice15
  · exact point40Slice16
  · exact point40Slice17
  · exact point40Slice18
  · exact point40Slice19
  · exact point40Slice20
  · exact point40Slice21
  · exact point40Slice22
  · exact point40Slice23
  · exact point40Slice24
  · exact point40Slice25
  · exact point40Slice26
  · exact point40Slice27
  · exact point40Slice28

set_option maxHeartbeats 1600000 in
private theorem point41Slice0 : pointSliceCheck 1 1552 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice1 : pointSliceCheck 1 1552 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice2 : pointSliceCheck 1 1552 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice3 : pointSliceCheck 1 1552 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice4 : pointSliceCheck 1 1552 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice5 : pointSliceCheck 1 1552 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice6 : pointSliceCheck 1 1552 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice7 : pointSliceCheck 1 1552 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice8 : pointSliceCheck 1 1552 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice9 : pointSliceCheck 1 1552 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice10 : pointSliceCheck 1 1552 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice11 : pointSliceCheck 1 1552 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice12 : pointSliceCheck 1 1552 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice13 : pointSliceCheck 1 1552 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice14 : pointSliceCheck 1 1552 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice15 : pointSliceCheck 1 1552 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice16 : pointSliceCheck 1 1552 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice17 : pointSliceCheck 1 1552 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice18 : pointSliceCheck 1 1552 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice19 : pointSliceCheck 1 1552 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice20 : pointSliceCheck 1 1552 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice21 : pointSliceCheck 1 1552 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice22 : pointSliceCheck 1 1552 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice23 : pointSliceCheck 1 1552 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice24 : pointSliceCheck 1 1552 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice25 : pointSliceCheck 1 1552 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice26 : pointSliceCheck 1 1552 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice27 : pointSliceCheck 1 1552 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice28 : pointSliceCheck 1 1552 28 := by
  decide +kernel

public theorem point41 : residualCheck 41 := by
  apply ofPointSlices 1 1552
  intro c
  fin_cases c
  · exact point41Slice0
  · exact point41Slice1
  · exact point41Slice2
  · exact point41Slice3
  · exact point41Slice4
  · exact point41Slice5
  · exact point41Slice6
  · exact point41Slice7
  · exact point41Slice8
  · exact point41Slice9
  · exact point41Slice10
  · exact point41Slice11
  · exact point41Slice12
  · exact point41Slice13
  · exact point41Slice14
  · exact point41Slice15
  · exact point41Slice16
  · exact point41Slice17
  · exact point41Slice18
  · exact point41Slice19
  · exact point41Slice20
  · exact point41Slice21
  · exact point41Slice22
  · exact point41Slice23
  · exact point41Slice24
  · exact point41Slice25
  · exact point41Slice26
  · exact point41Slice27
  · exact point41Slice28

set_option maxHeartbeats 1600000 in
private theorem point42Slice0 : pointSliceCheck 1 1559 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice1 : pointSliceCheck 1 1559 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice2 : pointSliceCheck 1 1559 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice3 : pointSliceCheck 1 1559 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice4 : pointSliceCheck 1 1559 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice5 : pointSliceCheck 1 1559 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice6 : pointSliceCheck 1 1559 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice7 : pointSliceCheck 1 1559 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice8 : pointSliceCheck 1 1559 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice9 : pointSliceCheck 1 1559 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice10 : pointSliceCheck 1 1559 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice11 : pointSliceCheck 1 1559 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice12 : pointSliceCheck 1 1559 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice13 : pointSliceCheck 1 1559 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice14 : pointSliceCheck 1 1559 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice15 : pointSliceCheck 1 1559 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice16 : pointSliceCheck 1 1559 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice17 : pointSliceCheck 1 1559 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice18 : pointSliceCheck 1 1559 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice19 : pointSliceCheck 1 1559 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice20 : pointSliceCheck 1 1559 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice21 : pointSliceCheck 1 1559 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice22 : pointSliceCheck 1 1559 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice23 : pointSliceCheck 1 1559 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice24 : pointSliceCheck 1 1559 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice25 : pointSliceCheck 1 1559 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice26 : pointSliceCheck 1 1559 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice27 : pointSliceCheck 1 1559 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice28 : pointSliceCheck 1 1559 28 := by
  decide +kernel

public theorem point42 : residualCheck 42 := by
  apply ofPointSlices 1 1559
  intro c
  fin_cases c
  · exact point42Slice0
  · exact point42Slice1
  · exact point42Slice2
  · exact point42Slice3
  · exact point42Slice4
  · exact point42Slice5
  · exact point42Slice6
  · exact point42Slice7
  · exact point42Slice8
  · exact point42Slice9
  · exact point42Slice10
  · exact point42Slice11
  · exact point42Slice12
  · exact point42Slice13
  · exact point42Slice14
  · exact point42Slice15
  · exact point42Slice16
  · exact point42Slice17
  · exact point42Slice18
  · exact point42Slice19
  · exact point42Slice20
  · exact point42Slice21
  · exact point42Slice22
  · exact point42Slice23
  · exact point42Slice24
  · exact point42Slice25
  · exact point42Slice26
  · exact point42Slice27
  · exact point42Slice28

set_option maxHeartbeats 1600000 in
private theorem point43Slice0 : pointSliceCheck 0 1684 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice1 : pointSliceCheck 0 1684 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice2 : pointSliceCheck 0 1684 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice3 : pointSliceCheck 0 1684 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice4 : pointSliceCheck 0 1684 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice5 : pointSliceCheck 0 1684 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice6 : pointSliceCheck 0 1684 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice7 : pointSliceCheck 0 1684 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice8 : pointSliceCheck 0 1684 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice9 : pointSliceCheck 0 1684 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice10 : pointSliceCheck 0 1684 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice11 : pointSliceCheck 0 1684 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice12 : pointSliceCheck 0 1684 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice13 : pointSliceCheck 0 1684 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice14 : pointSliceCheck 0 1684 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice15 : pointSliceCheck 0 1684 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice16 : pointSliceCheck 0 1684 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice17 : pointSliceCheck 0 1684 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice18 : pointSliceCheck 0 1684 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice19 : pointSliceCheck 0 1684 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice20 : pointSliceCheck 0 1684 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice21 : pointSliceCheck 0 1684 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice22 : pointSliceCheck 0 1684 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice23 : pointSliceCheck 0 1684 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice24 : pointSliceCheck 0 1684 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice25 : pointSliceCheck 0 1684 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice26 : pointSliceCheck 0 1684 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice27 : pointSliceCheck 0 1684 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice28 : pointSliceCheck 0 1684 28 := by
  decide +kernel

public theorem point43 : residualCheck 43 := by
  apply ofPointSlices 0 1684
  intro c
  fin_cases c
  · exact point43Slice0
  · exact point43Slice1
  · exact point43Slice2
  · exact point43Slice3
  · exact point43Slice4
  · exact point43Slice5
  · exact point43Slice6
  · exact point43Slice7
  · exact point43Slice8
  · exact point43Slice9
  · exact point43Slice10
  · exact point43Slice11
  · exact point43Slice12
  · exact point43Slice13
  · exact point43Slice14
  · exact point43Slice15
  · exact point43Slice16
  · exact point43Slice17
  · exact point43Slice18
  · exact point43Slice19
  · exact point43Slice20
  · exact point43Slice21
  · exact point43Slice22
  · exact point43Slice23
  · exact point43Slice24
  · exact point43Slice25
  · exact point43Slice26
  · exact point43Slice27
  · exact point43Slice28

set_option maxHeartbeats 1600000 in
private theorem point44Slice0 : pointSliceCheck 0 1688 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice1 : pointSliceCheck 0 1688 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice2 : pointSliceCheck 0 1688 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice3 : pointSliceCheck 0 1688 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice4 : pointSliceCheck 0 1688 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice5 : pointSliceCheck 0 1688 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice6 : pointSliceCheck 0 1688 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice7 : pointSliceCheck 0 1688 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice8 : pointSliceCheck 0 1688 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice9 : pointSliceCheck 0 1688 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice10 : pointSliceCheck 0 1688 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice11 : pointSliceCheck 0 1688 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice12 : pointSliceCheck 0 1688 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice13 : pointSliceCheck 0 1688 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice14 : pointSliceCheck 0 1688 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice15 : pointSliceCheck 0 1688 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice16 : pointSliceCheck 0 1688 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice17 : pointSliceCheck 0 1688 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice18 : pointSliceCheck 0 1688 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice19 : pointSliceCheck 0 1688 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice20 : pointSliceCheck 0 1688 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice21 : pointSliceCheck 0 1688 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice22 : pointSliceCheck 0 1688 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice23 : pointSliceCheck 0 1688 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice24 : pointSliceCheck 0 1688 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice25 : pointSliceCheck 0 1688 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice26 : pointSliceCheck 0 1688 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice27 : pointSliceCheck 0 1688 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice28 : pointSliceCheck 0 1688 28 := by
  decide +kernel

public theorem point44 : residualCheck 44 := by
  apply ofPointSlices 0 1688
  intro c
  fin_cases c
  · exact point44Slice0
  · exact point44Slice1
  · exact point44Slice2
  · exact point44Slice3
  · exact point44Slice4
  · exact point44Slice5
  · exact point44Slice6
  · exact point44Slice7
  · exact point44Slice8
  · exact point44Slice9
  · exact point44Slice10
  · exact point44Slice11
  · exact point44Slice12
  · exact point44Slice13
  · exact point44Slice14
  · exact point44Slice15
  · exact point44Slice16
  · exact point44Slice17
  · exact point44Slice18
  · exact point44Slice19
  · exact point44Slice20
  · exact point44Slice21
  · exact point44Slice22
  · exact point44Slice23
  · exact point44Slice24
  · exact point44Slice25
  · exact point44Slice26
  · exact point44Slice27
  · exact point44Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
