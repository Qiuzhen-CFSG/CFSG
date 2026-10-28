module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.AxisOrbits
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SourceComparisons

/-!
# Concrete Parker triality, spin, and natural–spin actions

The concrete Golay Parker loop gives the source permutations on triples with
an adjoined zero, the generated group `N`, its distinguished subgroups, and
the quotient `N/K`. The image of `Q1` is extraspecial of plus type and order
`2^25`, with the specified center and local centralizer. Here `K` is normal
in `N`; its centrality is relative to the even subgroup.

The actual `N1` action on the 4096-dimensional signed Parker-axis space is
monomial, preserves its positive form, has kernel `J`, and is irreducible
already on `Q1`. Restriction is an equivariant isometry to the displayed
`B1(A2) × B1(A3)`. Its even action is the product of the two half actions,
and odd first automorphisms exchange the halves with the source signs.
The `B3(A2)` action has its distinct specified three-generator kernel, and
the odd second automorphisms give the source transport from `B1(A2)`.

The actual 24-dimensional coordinate-halfspace action has kernel `Q1`.
Its tensor with spin has dimension 98304, is monomial, preserves the
positive definite tensor form, and has kernel exactly `K`. It gives faithful
actions of `N1/K` and its image in `N/K`. Tensoring the restriction isometry
proves the same statements in the displayed natural-by-direct-sum realization.
All normalization, quotient, scalar-action, and irreducibility premises are
discharged for the fixed carriers and homomorphisms.

Source: Aschbacher, *Sporadic Groups*, Section 14 and Section 27 through
Lemma 27.5, printed pp. 58–64 and 143–147. The action on the whole Griess
space and its algebra multiplication belong to the subsequent construction.
-/
