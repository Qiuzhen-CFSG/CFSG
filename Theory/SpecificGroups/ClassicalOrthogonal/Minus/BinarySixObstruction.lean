module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.ThreeRank
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Iwasawa
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Generation
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Primitive

/-!
# Intrinsic obstructions in the binary six-dimensional minus group

For the exact carrier `ClassicalGroup.POmegaMinus 3 (ZMod 2)`, the independent
anisotropic-plane rotations give an elementary abelian subgroup of order 27 in
the commutator group, injectively preserved by the literal scalar quotient.
`two_lt_primeRank_three` and `not_isMulCommutative` give the rank obstruction
and noncommutativity.

The Siegel transformations generate the orthogonal commutator group, which is
perfect. Their explicit action on the 27 singular points is primitive and
faithful. The abelian Siegel root subgroups therefore give simplicity by the
Iwasawa criterion, and the characteristic-two scalar-quotient isomorphism
transports it to the exact projective carrier. `isSimpleGroup` discharges every
input of the preserved conditional assembly theorem.

Source: Aschbacher--Smith A.2.15(2) and A.2.19 (`refs/quasithin.pdf`, printed
pp.37--41), with the Suz section identified in GLS3 Table 5.3o. The Chapter A
adapter and sporadic quotient constructions are separate consumers.
-/

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

/-- The actual orthogonal commutator group acts primitively on its singular points. -/
public theorem pointAction_isPreprimitive : MulAction.IsPreprimitive OmegaGroup Point :=
  pointAction_isPreprimitive_of_elementary_le elementary_eq_commutator.le

/-- The exact binary six-dimensional minus projective group is simple.
Generation, perfectness and singular-point primitivity are all proved intrinsically. -/
public theorem isSimpleGroup : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 (ZMod 2)) := by
  let := pointAction_isPreprimitive
  exact isSimpleGroup_of_geometry_and_generation elementary_eq_commutator omega_perfect

end ClassicalOrthogonal.Minus.BinarySixObstruction
