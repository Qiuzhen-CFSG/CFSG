module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Invariance
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Rank

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Assembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Source

/-!
# The component branch of the mixed-factor argument

This module eliminates the `F*(I) ≠ O₂(I)` branch under the raw mixed inputs
in Aschbacher–Smith 15.4.18, printed pp.1162–1163 of the combined
1 March 2004 manuscript.

`Classification` applies F.6.11 and the universal F.6.18 row interface to
the actual quotient I/O_{3′}(I), retaining every remaining alternative.
`Actions` constructs the faithful component action and proves characteristic
two for its actual fixed subgroups. `Sieve` eliminates the intrinsic models
except A₆ and constructs the S₆ inner extension. `StarTransport` identifies
that extension with the literal L*Z* subgroup of the source quotient.
`Selected` combines local recognition, the T-invariance argument and the
incompatible elementary two-rank bounds. The local results also identify
L with O²(I), keeping the three-prime core and residual distinct.

`ModelLifting` derives `IntrinsicComponentModel` for the original component
from every quotient row and the applicable 1.1.5 clauses, controlling the
central covering kernel. `Source.generalizedFitting_eq_twoCore_of_source`
(in the `ComponentBranch` namespace) discharges the model premise of
`Assembly` and proves F*(I) = O₂(I). The only classification input is the
authorized universal F.6.18 implication; F.6.11 and the needed residual
calculation are proved. The local invariance argument uses the proved
centralizer index, with the corrected complement C_Z(Y₁) instead of the
printed Z ∩ L.

The parent still supplies the realized mixed configuration and the genuine
earlier 1.1.5 conclusions. The remaining characteristic-two branch and
the final source theorem 15.4.18 stay with `TwoFactors`.
-/
