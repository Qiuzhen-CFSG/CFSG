module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.SourceExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.SymplecticInputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSevenOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MSOriginalCases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.CaseFourSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.CaseFourDistance
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.IntrinsicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MinimalIntrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.OriginalExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixOriginalAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixFixed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalContradiction

/-!
# The A₅ centralizer reduction: 13.6.2–23

The published part contains actual local subgroup and quotient notation,
the abelian-span implication from 13.5.10 and 13.5.12, the Baumann/Thompson
and Sylow-control deductions, and the singular-vector product reduction.
The latter already turns the main centralizer containment into both
conclusions of 13.6.7.

The symplectic branch of 13.6.6 is excluded from the actual earlier marked
configuration, whole-component equivalence and residual Borel placement.
The cubic residual forces even field degree, so field descent suffices for
the Thompson/Baumann argument and the literal torus-inverter contradiction.
The component adapter constructs the whole-model map from the precise I.1.3
universal-kernel input, rejects the rank-one source alternative and supplies
the specified Sylow and residual Borel placement. The multiplier and the
normalized-component classification remain part of the source assembly.

The original flag application now assembles the two containment branches
of 13.6.20, supplying A.3.12 from its proved full-catalogue producer
and retaining the genuine original local data and 13.3.2/13.6.3 inputs.
The rank-two A.3.18 application is proved for every surviving model.
The 13.6.21 noncontainment follows from the original trivial join-core
argument for every selected component, independently of its model.
The original A₆, G₂(2)′ and covered-A₆ cases of 13.6.22 are now excluded.
Their moving-plane, Sylow and checked-point inputs are constructed, and
Sylow averaging supplies the B.2.14 centralizing step. The earlier original
noncentrality theorem closes the first two cases; the covered-A₆ case uses
its proved marked-plane normalizer obstruction.
The exceptional-A₇ case is also excluded from the original inputs. Its
four-dimensional representation and the full permitted residual actor are
constructed on the source moving plane, retaining noncyclic actors. The
fixed-space calculation and Sylow averaging centralize the same earlier
marked conjugate, contradicting 13.6.17.
The ordinary linear-three block and ordinary A₇ block are now excluded from
the same original hypotheses. The latter constructs a six-point replacement
and compares fixed spaces on the actual original W_K; it does not assume that
the replacement is an A₆ block. The A₇ quotient-to-block selection is now
proved: the B.5 action on the original moved module, both C.1.24 seed
constructions and the characteristic-Baumann obstruction supply an ordinary
or exceptional A₇ block. Thus the A₇ plus quotient itself is excluded without
a block-selection premise. Other C.1.32 selections remain separate source
obligations. The A₆ source moved module has order 16 or 32, and the order-32
case is identified with the actual six-letter augmentation cover; whole-core
selection is still needed.

The minimal equal-star replacement is intrinsically quasisimple: radical
supplements and minimality force its radical quotient to have odd order,
excluding the nonquasisimple A.3.6 alternative. In the linear-three row this
constructs the original intrinsic model and MS-pair without a classification
callback. The case-four distance cannot equal four, since its Frattini
subgroup would lie in the center. The direct linear-three exclusion now
constructs the natural or doubled source module and checked-center identity
in all three core/distance cases. The original marked-point contradiction
and equal-star replacement exclude the actual SL₃(2) plus quotient, retaining
only genuine prescribed-path replacement as an additional MS input.

For the surviving rank-four route, `SourceOrthogonal.OriginalSource`
constructs the complete action configuration and applies the proved B.5.1
classification. It marks the actual six-dimensional moved section, the seed
stabilizer and the component centralizer with one actor, and proves that the
plus kernel is a two-group. `OriginalContradiction` identifies the actual
residual–Sylow image, transports the same moved section and proves the final
Thompson contradiction and nonsingular centralizer containment. The original
small-model exclusion and reduced SL₄/SL₅ catalogue remain explicit.

The remaining characteristic-two proof 13.6.6, the component selection 13.6.8–16,
and the component elimination 13.6.17–23 remain to be constructed and
assembled here. No source-numbered centralizer theorem is asserted yet.
The Section 13.6 owner must discharge every earlier-source input from
the genuine Hypothesis 13.3.1, including its uniform-A₅ implication.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.926–933.
-/
