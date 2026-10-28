module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.A6Exclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelNormalizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.CoverTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ScalarMovement

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceAssembly

/-!
# The marked triple-cover branch of 13.8.16(1)

The natural binary marking bounds the three-rank of the simple A₆ point
residual by one. Rank two therefore selects a genuine compatible model
L/O₂(L) ≃ Â₆, the concrete hexacode triple cover.

`SourceAssembly.source_tripleCover_and_automizer` combines this inference
with the exact equivalence of the image of `LinearThree.automizerAction`
with E₄. Its domain is N_M(L₁), for M = N_G(L), and it acts on the literal
L₁/O₂(L₁). The source-to-model marking, both cubic orders, preservation of
the two directions, the inner inverter and actual scalar motion are proved.
Scalar motion uses the preceding source wreath construction, through the
completed `SourceScalarAction` prerequisite; it does not use [L₁,T] = L₁.

The earlier compatible model alternative, factorization 13.2.2(3), moving
component data, and source clauses 13.8.13 and 13.7.3(9) remain explicit.
The containing source-theorem assembly supplies those earlier results.
The earlier conditional `ScalarMovement` API is preserved.

Source: Aschbacher–Smith, 13.8.16(1), printed p.952 (PDF p.969), standing
pp.946–947, and Notation 13.2.1 / Lemma 13.2.2, pp.877–878.
-/
