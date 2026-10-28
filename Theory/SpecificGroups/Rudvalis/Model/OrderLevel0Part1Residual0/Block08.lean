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
private theorem point40Slice0 : pointSliceCheck 1 1568 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice1 : pointSliceCheck 1 1568 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice2 : pointSliceCheck 1 1568 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice3 : pointSliceCheck 1 1568 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice4 : pointSliceCheck 1 1568 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice5 : pointSliceCheck 1 1568 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice6 : pointSliceCheck 1 1568 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice7 : pointSliceCheck 1 1568 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice8 : pointSliceCheck 1 1568 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice9 : pointSliceCheck 1 1568 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice10 : pointSliceCheck 1 1568 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice11 : pointSliceCheck 1 1568 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice12 : pointSliceCheck 1 1568 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice13 : pointSliceCheck 1 1568 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice14 : pointSliceCheck 1 1568 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice15 : pointSliceCheck 1 1568 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice16 : pointSliceCheck 1 1568 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice17 : pointSliceCheck 1 1568 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice18 : pointSliceCheck 1 1568 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice19 : pointSliceCheck 1 1568 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice20 : pointSliceCheck 1 1568 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice21 : pointSliceCheck 1 1568 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice22 : pointSliceCheck 1 1568 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice23 : pointSliceCheck 1 1568 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice24 : pointSliceCheck 1 1568 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice25 : pointSliceCheck 1 1568 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice26 : pointSliceCheck 1 1568 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice27 : pointSliceCheck 1 1568 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point40Slice28 : pointSliceCheck 1 1568 28 := by
  decide +kernel

public theorem point40 : residualCheck 40 := by
  apply ofPointSlices 1 1568
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
private theorem point41Slice0 : pointSliceCheck 1 1573 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice1 : pointSliceCheck 1 1573 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice2 : pointSliceCheck 1 1573 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice3 : pointSliceCheck 1 1573 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice4 : pointSliceCheck 1 1573 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice5 : pointSliceCheck 1 1573 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice6 : pointSliceCheck 1 1573 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice7 : pointSliceCheck 1 1573 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice8 : pointSliceCheck 1 1573 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice9 : pointSliceCheck 1 1573 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice10 : pointSliceCheck 1 1573 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice11 : pointSliceCheck 1 1573 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice12 : pointSliceCheck 1 1573 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice13 : pointSliceCheck 1 1573 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice14 : pointSliceCheck 1 1573 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice15 : pointSliceCheck 1 1573 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice16 : pointSliceCheck 1 1573 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice17 : pointSliceCheck 1 1573 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice18 : pointSliceCheck 1 1573 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice19 : pointSliceCheck 1 1573 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice20 : pointSliceCheck 1 1573 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice21 : pointSliceCheck 1 1573 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice22 : pointSliceCheck 1 1573 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice23 : pointSliceCheck 1 1573 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice24 : pointSliceCheck 1 1573 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice25 : pointSliceCheck 1 1573 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice26 : pointSliceCheck 1 1573 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice27 : pointSliceCheck 1 1573 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point41Slice28 : pointSliceCheck 1 1573 28 := by
  decide +kernel

public theorem point41 : residualCheck 41 := by
  apply ofPointSlices 1 1573
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
private theorem point42Slice0 : pointSliceCheck 0 1700 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice1 : pointSliceCheck 0 1700 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice2 : pointSliceCheck 0 1700 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice3 : pointSliceCheck 0 1700 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice4 : pointSliceCheck 0 1700 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice5 : pointSliceCheck 0 1700 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice6 : pointSliceCheck 0 1700 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice7 : pointSliceCheck 0 1700 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice8 : pointSliceCheck 0 1700 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice9 : pointSliceCheck 0 1700 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice10 : pointSliceCheck 0 1700 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice11 : pointSliceCheck 0 1700 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice12 : pointSliceCheck 0 1700 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice13 : pointSliceCheck 0 1700 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice14 : pointSliceCheck 0 1700 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice15 : pointSliceCheck 0 1700 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice16 : pointSliceCheck 0 1700 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice17 : pointSliceCheck 0 1700 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice18 : pointSliceCheck 0 1700 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice19 : pointSliceCheck 0 1700 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice20 : pointSliceCheck 0 1700 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice21 : pointSliceCheck 0 1700 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice22 : pointSliceCheck 0 1700 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice23 : pointSliceCheck 0 1700 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice24 : pointSliceCheck 0 1700 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice25 : pointSliceCheck 0 1700 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice26 : pointSliceCheck 0 1700 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice27 : pointSliceCheck 0 1700 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point42Slice28 : pointSliceCheck 0 1700 28 := by
  decide +kernel

public theorem point42 : residualCheck 42 := by
  apply ofPointSlices 0 1700
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
private theorem point43Slice0 : pointSliceCheck 0 1708 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice1 : pointSliceCheck 0 1708 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice2 : pointSliceCheck 0 1708 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice3 : pointSliceCheck 0 1708 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice4 : pointSliceCheck 0 1708 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice5 : pointSliceCheck 0 1708 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice6 : pointSliceCheck 0 1708 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice7 : pointSliceCheck 0 1708 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice8 : pointSliceCheck 0 1708 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice9 : pointSliceCheck 0 1708 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice10 : pointSliceCheck 0 1708 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice11 : pointSliceCheck 0 1708 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice12 : pointSliceCheck 0 1708 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice13 : pointSliceCheck 0 1708 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice14 : pointSliceCheck 0 1708 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice15 : pointSliceCheck 0 1708 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice16 : pointSliceCheck 0 1708 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice17 : pointSliceCheck 0 1708 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice18 : pointSliceCheck 0 1708 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice19 : pointSliceCheck 0 1708 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice20 : pointSliceCheck 0 1708 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice21 : pointSliceCheck 0 1708 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice22 : pointSliceCheck 0 1708 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice23 : pointSliceCheck 0 1708 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice24 : pointSliceCheck 0 1708 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice25 : pointSliceCheck 0 1708 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice26 : pointSliceCheck 0 1708 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice27 : pointSliceCheck 0 1708 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point43Slice28 : pointSliceCheck 0 1708 28 := by
  decide +kernel

public theorem point43 : residualCheck 43 := by
  apply ofPointSlices 0 1708
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
private theorem point44Slice0 : pointSliceCheck 0 1709 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice1 : pointSliceCheck 0 1709 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice2 : pointSliceCheck 0 1709 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice3 : pointSliceCheck 0 1709 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice4 : pointSliceCheck 0 1709 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice5 : pointSliceCheck 0 1709 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice6 : pointSliceCheck 0 1709 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice7 : pointSliceCheck 0 1709 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice8 : pointSliceCheck 0 1709 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice9 : pointSliceCheck 0 1709 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice10 : pointSliceCheck 0 1709 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice11 : pointSliceCheck 0 1709 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice12 : pointSliceCheck 0 1709 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice13 : pointSliceCheck 0 1709 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice14 : pointSliceCheck 0 1709 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice15 : pointSliceCheck 0 1709 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice16 : pointSliceCheck 0 1709 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice17 : pointSliceCheck 0 1709 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice18 : pointSliceCheck 0 1709 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice19 : pointSliceCheck 0 1709 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice20 : pointSliceCheck 0 1709 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice21 : pointSliceCheck 0 1709 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice22 : pointSliceCheck 0 1709 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice23 : pointSliceCheck 0 1709 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice24 : pointSliceCheck 0 1709 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice25 : pointSliceCheck 0 1709 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice26 : pointSliceCheck 0 1709 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice27 : pointSliceCheck 0 1709 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point44Slice28 : pointSliceCheck 0 1709 28 := by
  decide +kernel

public theorem point44 : residualCheck 44 := by
  apply ofPointSlices 0 1709
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

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
