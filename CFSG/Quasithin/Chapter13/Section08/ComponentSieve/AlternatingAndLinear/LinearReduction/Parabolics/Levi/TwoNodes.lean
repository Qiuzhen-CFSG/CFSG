module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.ResidualImages
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.SolvableFlags

/-!
# Nonadjacent two-node Levi calculations in binary five-space

The quotient API constructs the actual S₃ × S₃ quotient, with the supplied
node order and literal diagonal lifts. The two ambient node residuals have
images A₃ × 1 and 1 × A₃ in those same ordered factors. A solvable basis-flag
stabilizer with three-part nine deletes exactly two nonadjacent nodes;
the assembled theorem constructs its quotient with both residual markings.

The proofs use the general diagonal quotient of actual basis flags, the
perfectness of binary linear groups in dimensions at least three, and the
explicit cubic rotations on the two node coordinates.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.959–960 (PDF pp.976–977).
-/
