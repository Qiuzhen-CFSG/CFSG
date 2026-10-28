module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.Recognition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Coordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Containment
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Residuals
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.FactorRecognition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Lifting
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Decomposition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Splitting
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Mixed

/-!
# Local calculations in the surviving A₆/S₆ component case

Compatible coordinates for the actual quotient I/O_{3′}(I) yield
O^{3′}(I) = L, containment of both two-perfect factors in L, and the
centralizer index [C_{T_I}(Y_i):C_{T_I}(L)] = 2. The original factors
are A₄. Once the parent's invariance argument gives |C_{T_I}(L)| = 2,
the source elementary fixed planes construct actual E₄ × S₄ local groups.
The S₄ complements are the embedded intersections G_i ∩ L.

`Mixed` completes the local assembly from the realized mixed factors,
their constructed configuration, the source two-perfectness, |Z| = 4,
the faithful Z-action from 1.1.5, and the selected L ≃ A₆ and L*Z* ≃ S₆.
It constructs the whole-quotient coordinates, transports containment and
both centralizer indices to the ambient group, and applies `Invariance`
to prove C_{T_I}(L) = E₀ of order two. Both original factors are A₄,
and both original local groups are E₄ × S₄ with no extra splitting premise.
Model selection and the final rank contradiction remain with the parent.

The literal factor Z ∩ L printed on p.1163 fails in the standard S₆
calculation: `ComponentLocals.printed_factor_obstruction` exhibits a
double transposition which does not centralize the A₄ residual. The valid
central line is C_Z(Y); it gives the same proved index needed by `Invariance`.
`Mixed.first_centralizer_product` constructs this corrected ambient
multiplication map from the raw setup. The obstruction concerns the literal
intermediate calculation, not 15.4.18, whose full mixed configuration is contradictory.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed pp.1162–1163.
-/
