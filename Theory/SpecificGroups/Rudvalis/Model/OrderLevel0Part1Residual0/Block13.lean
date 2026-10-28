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
private theorem point65Slice0 : pointSliceCheck 0 1988 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice1 : pointSliceCheck 0 1988 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice2 : pointSliceCheck 0 1988 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice3 : pointSliceCheck 0 1988 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice4 : pointSliceCheck 0 1988 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice5 : pointSliceCheck 0 1988 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice6 : pointSliceCheck 0 1988 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice7 : pointSliceCheck 0 1988 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice8 : pointSliceCheck 0 1988 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice9 : pointSliceCheck 0 1988 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice10 : pointSliceCheck 0 1988 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice11 : pointSliceCheck 0 1988 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice12 : pointSliceCheck 0 1988 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice13 : pointSliceCheck 0 1988 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice14 : pointSliceCheck 0 1988 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice15 : pointSliceCheck 0 1988 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice16 : pointSliceCheck 0 1988 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice17 : pointSliceCheck 0 1988 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice18 : pointSliceCheck 0 1988 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice19 : pointSliceCheck 0 1988 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice20 : pointSliceCheck 0 1988 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice21 : pointSliceCheck 0 1988 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice22 : pointSliceCheck 0 1988 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice23 : pointSliceCheck 0 1988 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice24 : pointSliceCheck 0 1988 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice25 : pointSliceCheck 0 1988 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice26 : pointSliceCheck 0 1988 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice27 : pointSliceCheck 0 1988 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point65Slice28 : pointSliceCheck 0 1988 28 := by
  decide +kernel

public theorem point65 : residualCheck 65 := by
  apply ofPointSlices 0 1988
  intro c
  fin_cases c
  · exact point65Slice0
  · exact point65Slice1
  · exact point65Slice2
  · exact point65Slice3
  · exact point65Slice4
  · exact point65Slice5
  · exact point65Slice6
  · exact point65Slice7
  · exact point65Slice8
  · exact point65Slice9
  · exact point65Slice10
  · exact point65Slice11
  · exact point65Slice12
  · exact point65Slice13
  · exact point65Slice14
  · exact point65Slice15
  · exact point65Slice16
  · exact point65Slice17
  · exact point65Slice18
  · exact point65Slice19
  · exact point65Slice20
  · exact point65Slice21
  · exact point65Slice22
  · exact point65Slice23
  · exact point65Slice24
  · exact point65Slice25
  · exact point65Slice26
  · exact point65Slice27
  · exact point65Slice28

set_option maxHeartbeats 1600000 in
private theorem point66Slice0 : pointSliceCheck 0 1989 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice1 : pointSliceCheck 0 1989 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice2 : pointSliceCheck 0 1989 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice3 : pointSliceCheck 0 1989 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice4 : pointSliceCheck 0 1989 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice5 : pointSliceCheck 0 1989 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice6 : pointSliceCheck 0 1989 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice7 : pointSliceCheck 0 1989 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice8 : pointSliceCheck 0 1989 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice9 : pointSliceCheck 0 1989 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice10 : pointSliceCheck 0 1989 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice11 : pointSliceCheck 0 1989 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice12 : pointSliceCheck 0 1989 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice13 : pointSliceCheck 0 1989 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice14 : pointSliceCheck 0 1989 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice15 : pointSliceCheck 0 1989 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice16 : pointSliceCheck 0 1989 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice17 : pointSliceCheck 0 1989 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice18 : pointSliceCheck 0 1989 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice19 : pointSliceCheck 0 1989 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice20 : pointSliceCheck 0 1989 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice21 : pointSliceCheck 0 1989 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice22 : pointSliceCheck 0 1989 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice23 : pointSliceCheck 0 1989 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice24 : pointSliceCheck 0 1989 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice25 : pointSliceCheck 0 1989 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice26 : pointSliceCheck 0 1989 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice27 : pointSliceCheck 0 1989 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point66Slice28 : pointSliceCheck 0 1989 28 := by
  decide +kernel

public theorem point66 : residualCheck 66 := by
  apply ofPointSlices 0 1989
  intro c
  fin_cases c
  · exact point66Slice0
  · exact point66Slice1
  · exact point66Slice2
  · exact point66Slice3
  · exact point66Slice4
  · exact point66Slice5
  · exact point66Slice6
  · exact point66Slice7
  · exact point66Slice8
  · exact point66Slice9
  · exact point66Slice10
  · exact point66Slice11
  · exact point66Slice12
  · exact point66Slice13
  · exact point66Slice14
  · exact point66Slice15
  · exact point66Slice16
  · exact point66Slice17
  · exact point66Slice18
  · exact point66Slice19
  · exact point66Slice20
  · exact point66Slice21
  · exact point66Slice22
  · exact point66Slice23
  · exact point66Slice24
  · exact point66Slice25
  · exact point66Slice26
  · exact point66Slice27
  · exact point66Slice28

set_option maxHeartbeats 1600000 in
private theorem point67Slice0 : pointSliceCheck 0 1996 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice1 : pointSliceCheck 0 1996 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice2 : pointSliceCheck 0 1996 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice3 : pointSliceCheck 0 1996 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice4 : pointSliceCheck 0 1996 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice5 : pointSliceCheck 0 1996 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice6 : pointSliceCheck 0 1996 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice7 : pointSliceCheck 0 1996 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice8 : pointSliceCheck 0 1996 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice9 : pointSliceCheck 0 1996 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice10 : pointSliceCheck 0 1996 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice11 : pointSliceCheck 0 1996 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice12 : pointSliceCheck 0 1996 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice13 : pointSliceCheck 0 1996 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice14 : pointSliceCheck 0 1996 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice15 : pointSliceCheck 0 1996 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice16 : pointSliceCheck 0 1996 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice17 : pointSliceCheck 0 1996 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice18 : pointSliceCheck 0 1996 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice19 : pointSliceCheck 0 1996 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice20 : pointSliceCheck 0 1996 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice21 : pointSliceCheck 0 1996 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice22 : pointSliceCheck 0 1996 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice23 : pointSliceCheck 0 1996 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice24 : pointSliceCheck 0 1996 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice25 : pointSliceCheck 0 1996 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice26 : pointSliceCheck 0 1996 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice27 : pointSliceCheck 0 1996 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point67Slice28 : pointSliceCheck 0 1996 28 := by
  decide +kernel

public theorem point67 : residualCheck 67 := by
  apply ofPointSlices 0 1996
  intro c
  fin_cases c
  · exact point67Slice0
  · exact point67Slice1
  · exact point67Slice2
  · exact point67Slice3
  · exact point67Slice4
  · exact point67Slice5
  · exact point67Slice6
  · exact point67Slice7
  · exact point67Slice8
  · exact point67Slice9
  · exact point67Slice10
  · exact point67Slice11
  · exact point67Slice12
  · exact point67Slice13
  · exact point67Slice14
  · exact point67Slice15
  · exact point67Slice16
  · exact point67Slice17
  · exact point67Slice18
  · exact point67Slice19
  · exact point67Slice20
  · exact point67Slice21
  · exact point67Slice22
  · exact point67Slice23
  · exact point67Slice24
  · exact point67Slice25
  · exact point67Slice26
  · exact point67Slice27
  · exact point67Slice28

set_option maxHeartbeats 1600000 in
private theorem point68Slice0 : pointSliceCheck 0 1997 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice1 : pointSliceCheck 0 1997 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice2 : pointSliceCheck 0 1997 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice3 : pointSliceCheck 0 1997 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice4 : pointSliceCheck 0 1997 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice5 : pointSliceCheck 0 1997 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice6 : pointSliceCheck 0 1997 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice7 : pointSliceCheck 0 1997 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice8 : pointSliceCheck 0 1997 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice9 : pointSliceCheck 0 1997 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice10 : pointSliceCheck 0 1997 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice11 : pointSliceCheck 0 1997 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice12 : pointSliceCheck 0 1997 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice13 : pointSliceCheck 0 1997 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice14 : pointSliceCheck 0 1997 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice15 : pointSliceCheck 0 1997 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice16 : pointSliceCheck 0 1997 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice17 : pointSliceCheck 0 1997 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice18 : pointSliceCheck 0 1997 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice19 : pointSliceCheck 0 1997 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice20 : pointSliceCheck 0 1997 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice21 : pointSliceCheck 0 1997 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice22 : pointSliceCheck 0 1997 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice23 : pointSliceCheck 0 1997 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice24 : pointSliceCheck 0 1997 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice25 : pointSliceCheck 0 1997 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice26 : pointSliceCheck 0 1997 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice27 : pointSliceCheck 0 1997 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point68Slice28 : pointSliceCheck 0 1997 28 := by
  decide +kernel

public theorem point68 : residualCheck 68 := by
  apply ofPointSlices 0 1997
  intro c
  fin_cases c
  · exact point68Slice0
  · exact point68Slice1
  · exact point68Slice2
  · exact point68Slice3
  · exact point68Slice4
  · exact point68Slice5
  · exact point68Slice6
  · exact point68Slice7
  · exact point68Slice8
  · exact point68Slice9
  · exact point68Slice10
  · exact point68Slice11
  · exact point68Slice12
  · exact point68Slice13
  · exact point68Slice14
  · exact point68Slice15
  · exact point68Slice16
  · exact point68Slice17
  · exact point68Slice18
  · exact point68Slice19
  · exact point68Slice20
  · exact point68Slice21
  · exact point68Slice22
  · exact point68Slice23
  · exact point68Slice24
  · exact point68Slice25
  · exact point68Slice26
  · exact point68Slice27
  · exact point68Slice28

set_option maxHeartbeats 1600000 in
private theorem point69Slice0 : pointSliceCheck 0 1999 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice1 : pointSliceCheck 0 1999 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice2 : pointSliceCheck 0 1999 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice3 : pointSliceCheck 0 1999 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice4 : pointSliceCheck 0 1999 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice5 : pointSliceCheck 0 1999 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice6 : pointSliceCheck 0 1999 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice7 : pointSliceCheck 0 1999 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice8 : pointSliceCheck 0 1999 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice9 : pointSliceCheck 0 1999 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice10 : pointSliceCheck 0 1999 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice11 : pointSliceCheck 0 1999 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice12 : pointSliceCheck 0 1999 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice13 : pointSliceCheck 0 1999 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice14 : pointSliceCheck 0 1999 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice15 : pointSliceCheck 0 1999 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice16 : pointSliceCheck 0 1999 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice17 : pointSliceCheck 0 1999 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice18 : pointSliceCheck 0 1999 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice19 : pointSliceCheck 0 1999 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice20 : pointSliceCheck 0 1999 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice21 : pointSliceCheck 0 1999 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice22 : pointSliceCheck 0 1999 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice23 : pointSliceCheck 0 1999 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice24 : pointSliceCheck 0 1999 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice25 : pointSliceCheck 0 1999 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice26 : pointSliceCheck 0 1999 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice27 : pointSliceCheck 0 1999 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point69Slice28 : pointSliceCheck 0 1999 28 := by
  decide +kernel

public theorem point69 : residualCheck 69 := by
  apply ofPointSlices 0 1999
  intro c
  fin_cases c
  · exact point69Slice0
  · exact point69Slice1
  · exact point69Slice2
  · exact point69Slice3
  · exact point69Slice4
  · exact point69Slice5
  · exact point69Slice6
  · exact point69Slice7
  · exact point69Slice8
  · exact point69Slice9
  · exact point69Slice10
  · exact point69Slice11
  · exact point69Slice12
  · exact point69Slice13
  · exact point69Slice14
  · exact point69Slice15
  · exact point69Slice16
  · exact point69Slice17
  · exact point69Slice18
  · exact point69Slice19
  · exact point69Slice20
  · exact point69Slice21
  · exact point69Slice22
  · exact point69Slice23
  · exact point69Slice24
  · exact point69Slice25
  · exact point69Slice26
  · exact point69Slice27
  · exact point69Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
