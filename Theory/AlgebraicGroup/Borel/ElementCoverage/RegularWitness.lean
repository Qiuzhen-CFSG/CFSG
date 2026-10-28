module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.Cartan

/-!
# A connected solvable subgroup with a regular fixed-coset witness

Over any algebraically closed field, `exists_connectedSolvable_regularWitness`
constructs a connected solvable closed subgroup `H` and an element of `H`
with finitely many fixed points on the actual homogeneous space `G / H`.
In particular this supplies the witness needed by the density argument for
connected algebraic groups, independently of the characteristic.

Choose a maximal torus `T` and put `H = C_G(T)^0`. The Cartan structure
proves nilpotence of `H` and `N_G(H)^0 = H`. A point of `T` separating the
finitely many representation weights has `C_G(t)^0 = H`. Its transporter
into `H` lies in `N_G(H)`, so the fixed cosets are an image of the finite
component quotient `N_G(H) / H`.

`RegularWitness.FixedCosets` retains the general finite-quotient reductions
and their conditional interfaces; `RegularWitness.Cartan` discharges all
Cartan and regular-element premises. This module re-exports both, together
with the reusable identity-component structure from §11.7. Ambient
connectedness is needed only by the subsequent density argument.

Source: Borel, *Linear Algebraic Groups*, second edition,
`refs/KGroup/Bor1/Chapter4.tex`, §§11.5, 11.7, 11.9(2) and the first two
paragraphs of §11.10; `refs/KGroup/Bor1/Chapter3.tex`, §8.18.
-/
