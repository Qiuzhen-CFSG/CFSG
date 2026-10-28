module

public import Theory.GroupTheory.CharacteristicLocalSylow
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ResidualModels
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.CenterFree
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Paired
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FixedPlane
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.MarkedPlane
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ThompsonMarking
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.BaumannGeometry
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FactorStabilizers
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FactorFixedSpaces
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction

/-!
# Preliminary results for the A₅ and A₆ cases: elementary bridges

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, §13.2, printed pp.876–884.
The proof of its main result, Theorem 13.2.7, ends on p.884.

The characteristic-normalizer criterion supplies the Sylow enlargement
and nonfusion arguments in 13.2.6. The Klein-four action lemma supplies
the fixed-point argument on invariant summands in 13.2.14. Both use
explicit mathematical inputs, to be discharged in the source applications.

The full ten-clause A₆ result 13.2.2, the A₅ local analysis 13.2.3–6,
and the remaining counterexample analysis 13.2.8–14 are needed to assemble
Theorem 13.2.7. The source 13.2.9 kernel step is now proved: the original
omega-orbit centralizer and overlap core equal O₂(H), and the intrinsic
residual core quotient is the exact C₃ or E₉ model. The wreath residual cannot
lie in a faithful local component, giving the component exclusion of 13.2.10.
The Baumann bound is supplied from the genuine 4.3.2 uniqueness premise.
That earlier uniqueness and solvability remain explicit; no even-action
or E.2.1 callback remains.

The original Context also supplies the complete 5.2.3 setup. For an outside
H moving the omega center, the centralizing local alternative is impossible;
if n(H)>1, the genuine earlier 5.2.3 theorem therefore gives a complete Main
Theorem model. This reduction retains that earlier theorem and the parameter
lower bound, and does not assert the missing solvability conclusion 13.2.8(1).
-/
