module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.TIAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.Transfer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.OddCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CentralizerConsequences
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FusionReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.SourceObstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.JointCentralizer

/-!
# The diagonal-outer branch of the component argument

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 15.3.38, printed pp.1135--1137: if `m₃(L) = 2`, then `Y₊ ≤ L`.

The checked reductions here establish the TI criterion, assertion (*),
the graph-field nonfusion step using its actual centralizer action, the
odd-core containment and its transport along fusion, and the transfer
trichotomy. `FusionReduction` combines these steps with a graph-centralizer
component to force the field-involution fusion class.
`CentralizerConsequences` also proves the elementary exponent-three obstruction
for both alternatives in the component-centralizer theorem. `FieldModels`
publishes those alternatives with actual group isomorphisms.
`SourceObstruction` proves that the printed construction of the order-27
input conflicts with the earlier plane-centralizer description.
`JointCentralizer` repairs that construction: the earlier index-two inclusion
and graph-field centralizer model give an actual E₉ joint two-residual,
transported by fusion. It is also the joint odd core, and its order already
suffices for the elementary exclusion. The field-component argument must still
establish the opposing containment. Their inputs are direct
subgroup, conjugation, and quotient hypotheses.

Full assembly still requires the reduction to the central cover of L₃(4),
the actual diagonal/graph/field model facts, the component in the graph
centralizer that excludes the `z` class, and the final field-centralizer
component argument. No numbered theorem
15.3.38 is exported until these inputs have been constructed. The final
Section 15.3 uniqueness assembly remains in `ComponentUniqueness`.
-/
