module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Families
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Baumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Application
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Assembly

/-!
# Ordinary A₇: the W_K action and fixed-vector comparison

`ModuleComparison.representation` is the faithful binary representation of
the literal plus quotient on W_K restricted to the plus actor. Its kernel
and its fixed vectors use the actual ambient centralizers. The seed span
is identified with ⟨z^K⟩ under the source normalization and containment.

`ordinaryNaturalSummand` constructs an equivariant natural summand and
fixed complement from the SAME chosen ordinary block model. The component
splitting uses vanishing first cohomology and the seed span; the normalizer
extension preserves its coordinates on the full plus actor.

`ordinary_comparison_exists` supplies the faithful compatible action, the
fixed-codimension comparison for every subgroup, and the fixed-centralizer
bound and Baumann/J equality for any simultaneous three-transposition
marking. The earlier identity [W_K,K] = [Z(O₂(K)),K] remains explicit with
its original source producers. The parent retains its discharge and the
offender-family marking; this module supplies the actual module comparison
needed there, not the entire Lemma 13.6.22.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.3.3(1),
printed p.84, and 13.6.22, printed p.932 (PDF p.949).
-/
