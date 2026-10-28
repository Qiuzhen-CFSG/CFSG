module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FrattiniObstruction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.QuotientActions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.SourceObstruction

/-!
# Model-valued quotient deductions in §1.2

The full A.3.12 embedding-list deduction, including unique containment and
relative normality, is proved in `lemma_1_2_4_of_A_3_12_A_3_8`. Its inputs are
the universal earlier results and the SQTK hypothesis on the local quotient.

`proposition_1_2_1_four_reduction` applies the complete A.3.6 contract and
isolates the extra center–Frattini equality printed in 1.2.1(4d). That equality
is not part of the displayed A.3.6 conclusion. The now fully instantiated
`CenterFrattiniSource.intrinsic_counterexample_with_omega_actions` shows that
even the complete A.3.6 hypotheses, common clauses and actual omega-action
data do not imply it. The reduction is not a completed proof of the printed
Proposition 1.2.1(4): its remaining branch requires the simple QTKE ambient
setup, which is not realized by the counterexample.

`proposition_1_2_1_four_earlier_with_actions` gives the full earlier structural
conclusion and the actual omega-action data for the image of the specified
component. This valid strengthening is available independently of the missing
center–Frattini equality.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.43–48, 504–505.
-/
