module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Baumann

/-!
# Orthogonal local preliminaries for Section 15.3

The checked transport gives the elementary rank-four module, its planes of
order four, and elementary fixed planes contained in their Sylow stabilizers.
The residual argument includes the essential Sylow supplement omitted in the
printed proof of 15.3.2(3). It derives the two-maximal-overgroup result and
`Mc=C_G(Z)` from the precise Chapter 14 ordering inputs and maximality of the
concrete Sylow image. The Baumann arguments prove 15.3.3 and the centralizing
alternative of 15.3.5; local Sylow indices give all conclusions of 15.3.6.

Earlier-source inputs are the compatible natural action from 15.1.3, the
ordering-maximality and domination of 14.1.12, and the nontrivial
characteristic `C₂` with its factorization from 14.1.11. The Section 15.3
parent must instantiate these under genuine Hypothesis 14.1.5, its
counterexample assumption, and `M=Mf`.

The full 15.3.2–6 assembly remains here. Required missing calculations are
maximality of the concrete Sylow image, fixed-line and fixed-plane orders,
the index-two stabilizer and its two local Sylow indices, and the particular
noncentral Thompson alternative. The last clause of 15.3.2(6) also retains
all of B.6.8 and, when nonsolvable, E.2.2; proving the minimal-parabolic
predicate alone does not discharge those descriptions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, PDF pp.1138–1139. Final 15.3.2–12 assembly belongs to
`Preliminaries.lean`.
-/
