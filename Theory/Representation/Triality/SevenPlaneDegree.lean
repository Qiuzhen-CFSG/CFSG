module

public import Theory.Representation.BinarySevenPlaneDegree
public import Theory.SpecificGroups.Triality.BinarySevenPlane
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The seven-plane degree bound on the genuine binary triality carrier

Apply the quaternion and Frobenius weight argument to the literal carrier
`Standard.BinaryCarrier 1`. The explicit seven-plane construction supplies
the embedded subgroup and its two ambient conjugating elements, so the final
degree bound has no subgroup-construction premise. Faithfulness suffices;
irreducibility is unnecessary.

This is the q = 2 degree ingredient of Aschbacher--Smith, G.9.3, printed
p.356. It does not assert the separate general lower bound 24*n.
-/

public section

namespace Triality.SevenPlaneDegree

/-- The marked subgroup in the actual carrier forces binary degree at least 24. -/
theorem finrank_ge_of_data
    (d : QuaternionSevenPlane.Data (Standard.BinaryCarrier 1 Nat.zero_lt_one))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) (Standard.BinaryCarrier 1 Nat.zero_lt_one) V)
    (hrho : Function.Injective rho) : 24 ≤ Module.finrank (ZMod 2) V :=
  Representation.BinarySevenPlaneDegree.finrank_ge rho hrho d

/-- Every faithful binary representation of the genuine triality carrier at
field order two has dimension at least 24. -/
theorem finrank_ge
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) (Standard.BinaryCarrier 1 Nat.zero_lt_one) V)
    (hrho : Function.Injective rho) : 24 ≤ Module.finrank (ZMod 2) V :=
  finrank_ge_of_data Standard.binarySevenPlane rho hrho

end Triality.SevenPlaneDegree
