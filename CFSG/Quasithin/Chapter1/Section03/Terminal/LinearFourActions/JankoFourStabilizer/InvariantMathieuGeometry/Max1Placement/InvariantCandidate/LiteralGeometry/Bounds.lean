module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Transport

/-!
# Remaining binary geometry for intrinsic max1 recovery

Write V for the elementary two-core of the literal max1 subgroup, P for
an octad stabilizer in its native M₂₄ quotient, Q for the preimage of
O₂(P), and R for the solvable residual of the preimage of P.

The three propositions below are unproved geometric obligations. Individual
elements of Q outside V should fix at most 128 elements of V, while Q
itself should fix fewer than 128. The center of O₂(R) should lie in V
and its centralizer in max1 should lie in Q. These statements retain the
actual quotient map and embedded intrinsic cores; they assume no splitting.

`LiteralGeometry` proves that these obligations, together with common-octad
placement, imply intrinsic recovery. The source statement is not established
until the obligations are supplied by proofs on the binary model.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the local
configuration in the proof of 1.3.9, p.514; GLS3 Table 5.3i.
-/

public section

open Subgroup Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

/-- The rank-four lower bound for a nonidentity octad-kernel action on V. -/
@[expose] def LiteralOctadElementFixedBound : Prop :=
  ∀ (O : Octad) (x : certifiedMathieuSubgroup),
    x ∈ literalOctadTwoPreimage O → x ∉ pCore 2 certifiedMathieuSubgroup →
      Nat.card ((centralizer ({x} : Set certifiedMathieuSubgroup)).subgroupOf
        (pCore 2 certifiedMathieuSubgroup)) ≤ 128

/-- The common fixed space is strictly smaller than the individual bound. -/
@[expose] def LiteralOctadCommonFixedBound : Prop :=
  ∀ O : Octad,
    Nat.card ((centralizer (literalOctadTwoPreimage O : Set certifiedMathieuSubgroup)).subgroupOf
      (pCore 2 certifiedMathieuSubgroup)) < 128

/-- The two center containments needed for the elementary-subgroup argument. -/
@[expose] def LiteralOctadCenterBounds : Prop :=
  ∀ O : Octad,
    coreCenter (literalOctadResidual O) ≤ pCore 2 certifiedMathieuSubgroup ∧
      centralizer (coreCenter (literalOctadResidual O) : Set certifiedMathieuSubgroup) ≤
        literalOctadTwoPreimage O

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
