module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.NormalizerTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.Exclusion

/-!
# The covered-A₆ branch of Lemma 13.6.22

The original six-dimensional binary block action, its three-dimensional F₄
structure, and actual hexacode coordinates are constructed from the exceptional
block predicate. The source Thompson/Baumann marking supplies the projective
F₄-line U₂ (vector dimension two), with its literal normalizer-image equality
and ambient placement in Mᵥ.

The concrete plane-normalizer calculation excludes every invariant order-four
subgroup of U. Applied to the actual source commutator l=[V,Lᵥ], it proves
`CoveredSix.not_exceptional_of_localConfiguration`. The representation,
marking and normalizer conclusions are discharged internally; only the genuine
earlier local source conclusions remain inputs. The other small-model branches
and C.1 case selection remain with `AlternatingBranches`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.932–933.
-/
