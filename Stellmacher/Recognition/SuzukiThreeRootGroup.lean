module

public import Stellmacher.Recognition.SuzukiThreeRootExponent
public import Stellmacher.Recognition.SuzukiThreeRootNoncommuting

/-!
# Suzuki's root group at q = 3

Both exponent three and noncommutativity follow from the original action
hypotheses. The exponent proof uses the order-eight torus automorphism and
the fixed points of its fourth power. The noncommutativity proof excludes
abelian ternary root coordinates using the fifth-power swapping involution
and the finite affine stabilizer obstruction.

This module is the public assembly boundary for the root-group conclusions.
It re-exports `SuzukiThreeHypotheses.root_cube` and
`SuzukiThreeHypotheses.root_noncommuting`.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section II, Lemma 8, and Section III, Lemmas 9–12.
-/
