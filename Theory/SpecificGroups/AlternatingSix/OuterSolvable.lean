module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The outer automorphism group of A₆ is solvable

The actual inner automorphism subgroup has index four in `Aut(A₆)`.
Thus its quotient is a group of order four and is commutative, hence solvable.
The index calculation in `ShadowLocal.Basic` uses the faithful S₆ action
and its index two, proved by the concrete exceptional automorphism of A₆.

Source: GLS3, Theorem 5.2.1(b), applied to the A₆ alternative in the
extension-control argument of Theorem 6.5.3. No splitting is asserted or used.
-/

namespace AlternatingSix.ShadowLocal

/-- The actual quotient `Aut(A₆)/Inn(A₆)` has order four. -/
public theorem outer_card : Nat.card (MulAut.Outer A6) = 4 := inner_index

/-- Every two classes in `Aut(A₆)/Inn(A₆)` commute. -/
public theorem outer_isMulCommutative : IsMulCommutative (MulAut.Outer A6) :=
  IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) outer_card

/-- Solvability of the actual outer automorphism group of A₆. -/
public theorem outer_isSolvable : Group.IsSolvable (MulAut.Outer A6) :=
  Group.isSolvable_of_comm outer_isMulCommutative.is_comm.comm

end AlternatingSix.ShadowLocal
