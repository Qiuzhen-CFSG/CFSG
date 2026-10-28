module

public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOrbitSpan
public import CFSG.Quasithin.ChapterB.Section04.G2

/-!
# Small quadratic and cubic representation ratios

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.4, printed pp. 85–98.

The duality input B.4.7 is provided by `Theory.Representation.QuadraticDuality`:
annihilators exchange fixed and commutator spaces, so quadratic actions persist
under duality, with the required equality of dimensions. The general
annihilator order anti-isomorphism is `Subspace.orderIsoFiniteDimensional`.

The spanning-orbit result B.4.12(1) is
`Representation.orbit_eq_nonzero_of_pair_transitive`. Its proof closes the orbit
under addition after adjoining zero, then uses the spanning hypothesis.
-/
