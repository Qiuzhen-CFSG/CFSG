module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeConstraints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeZArithmetic.Certificates

/-!
# Exclusion of a large ratio at the final constituent

The restriction congruence and `|z| < 4c²` leave exactly 28 signed rows.
For each, denominator divisibility and the quadratic obtained by substituting
`y=x+z+1` give a complete finite exclusion. All signs and both final unit
multiplicities are retained. No additional numerical premise is required.

The source-theorem assembly constructs `S` using `caseTwo_integerSystem` and
obtains the bound from `caseTwo_large_degree_bound` at constituent 5.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion

/-- The large-ratio branch at the final constituent of case two is impossible. -/
public theorem caseTwo_largeZ_impossible {g : ℕ} {x y z a b c : ℤ}
    (S : CaseTwoIntegerSystem g x y z a b c)
    (hr : (z.natAbs : ℤ) < 4*c^2) : False :=
  LargeZ.rows_impossible S (LargeZ.zRow_mem S.row_z hr)

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
