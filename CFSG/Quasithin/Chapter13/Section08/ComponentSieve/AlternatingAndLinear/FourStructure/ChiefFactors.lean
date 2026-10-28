module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Heads
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Codimension
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceHeads
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Assembly

/-!
# The L₄ head and chief-factor argument

`SourceHeads` proves the common natural head identifications and uniqueness
for the literal source action, including the marked plane and an irreducible
submodule in the nonzero maximal kernel when the whole module is not natural.
It constructs the generating seed from the actual conjugate span and uses
the natural Sylow fixed-line calculation.

`Sections` checks B.4 on every noncentral chief section and passes absence of
offenders from a factor to the maximal submodule. `SourceSix` then gives the
actual A₁ containment, equality Uγ*=Vγ*≅E₄, and the codimension equalities,
using the marked six-dimensional actor calculation in `MarkedSix`.
`SixSymmetry` constructs the reversed critical pair, proves its eligibility,
and obtains V₁≤Uγ and the strict inclusion Uγ*<Vγ*. The `source_chief_factors`
theorem in `Assembly` combines these deductions to exclude exterior-square factors and applies
`CentralExclusion` to remove central factors. All chief factors are identified
equivariantly as natural or dual under the same actor equivalence, and hence
have dimension four.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed pp.960–961, PDF pp.977–978.

The assembly retains the genuine earlier source and selected critical-pair
inputs and the universal B.4 classification. The six-factor actor, reversal,
strict inclusion, and cohomology steps are discharged. It does not use the
conditional `SixFactorInput` certificate as an earlier hypothesis. The later
argument proving that the entire module is natural is outside this module.
-/
