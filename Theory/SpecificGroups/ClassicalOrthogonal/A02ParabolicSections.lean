module

public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.BinaryD4
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction

/-!
# Orthogonal local obstructions and binary section targets

The binary split rank-four endpoint has an explicit proper involution
centralizer containing an elementary abelian subgroup of order 27.
For sections occurring in higher orthogonal ranks, this interface also
reexports the intrinsic nonabelian simplicity and 3-rank bounds of the
actual binary minus-six and split-eight projective carriers.

The endpoint uses a local rank obstruction directly. The other two targets
are intended as semisimple sections; their occurrence in higher-rank
parabolics requires separate geometric constructions.

Source: Aschbacher–Smith A.2.18, printed p.40 (`refs/quasithin.pdf`),
and GLS3 §2.6. The source application uses A.2.15(2) through the
literal central quotient G/Z(G).
-/
