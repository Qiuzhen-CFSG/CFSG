module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.ChecksX
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.ChecksY

/-!
# Complete kernel verification of the large-X and large-Y searches

`ChecksX` verifies all 29 selected X rows; `ChecksY` verifies all 56 selected
Y rows. Both use proved divisor and root coverage and retain every original
multiplicity and cofactor condition. Checks are split at multiplicity pairs
to bound kernel memory; selected-row coverage is itself kernel-checked.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/
