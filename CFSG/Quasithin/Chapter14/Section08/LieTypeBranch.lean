module

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.Assembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SourceCounterexample
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.BinaryLieModels
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.LinearRank

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.UnitaryFive

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.RankOneExclusion
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource

/-!
# The Lie-type branch of Theorem D

`rankTwoModel_of_binaryLieModel` proves the complete known Lie-type branch
of Theorem D/14.8.2(1), printed pp.1078–1079 of Aschbacher–Smith. From the
original simple QTKE hypothesis, nonempty actual faithful local family and
an actual characteristic-two Lie model at exponent `n > 1`, it constructs
the allowed rank-two model at the same exponent, with U₅ only when `n = 2`.

The rank-one Borel argument and direct root-normalizer obstructions exclude
all unwanted ranks and families. Actual orthogonal comparisons handle the
low-rank aliases, and the unitary-five torus gives the parameter restriction.
The assembly retains the genuine triality and general Ree F₄ alternatives.
`theoremDModel_of_binaryLieModel` supplies the full D-model conclusion, and
`exists_counterexample_of_not_theoremDModel` constructs the existing Chapter 13
standing counterexample, including the unrestricted Lie-family exclusion,
all exceptional-model exclusions and the uniform A₅ quotient choice.
The remaining local recognition arguments must eliminate that configuration.

The ordinary natural-six source now supplies its Baumann normalizer bound
internally. Its plus-kernel, abelian full-span and critical-geometry consumers
retain the genuine earlier plane and 13.3.2 classification inputs.
-/
