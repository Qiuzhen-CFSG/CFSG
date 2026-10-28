module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.KnownSimple

/-!
# Source containment and star-action reductions

The completed preliminary deductions prove cubic generation of L_v,
nonvanishing of [U_K,L_v] on the actual module carrier, and the passage
from a nonzero plus commutator to the star-action obstruction and K ⊄ M.

The source rank-two branch now proves its required A.3.18 application
on the seven surviving concrete models. The L₃(2) branch,
exported through `SourceContainment.LinearThree`, derives its ambient
normalization and containment from the original marked local data and
genuine earlier A.3.12, 13.3.2 and 13.6.3 inputs. Its module, normal-cover
and projection premises are discharged by the source application.
`OriginalSource` combines both branches with no A.3.18 callback and
proves K ⊄ N(L) from the earlier trivial join-core result for all models.
`KnownSimple` supplies A.3.12 from its proved full-catalogue producer,
giving both original conclusions with no component-classification callback.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.931–932. The final assembly belongs here; independent source
case extensions should import `SourceContainment.Basic`.
-/
