module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Applications
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Constituents

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Recognition

/-!
# Source recognition for the exchanged field-four branch

The original hypotheses supply the literal exchanged PSL₂(4) actor, a faithful
irreducible maximal source quotient, zero fixed spaces for its two components,
and the F.9 quadratic bound. Homogeneous orbit classification and actual
factor exchange identify that entire quotient with the natural orthogonal
module. The non-FF and commuting-cubic arguments lift the identification to
all of U_H/V₁.

`SourceRecognition.source_module_alternatives` proves the requested literal
alternatives. `SourceRecognition.source_recognition` applies them to
`Original.orthogonal_of_module_alternatives`. Both the group equivalence and
the intertwining linear equivalence concern the whole original module;
no classification callback or extra model premise remains. The final
geometric contradiction is left to the original source assembly.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/
