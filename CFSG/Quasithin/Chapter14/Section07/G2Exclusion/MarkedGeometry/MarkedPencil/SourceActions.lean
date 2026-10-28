module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Points
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Offenders
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualLift
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Assembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.QuotientOffenders

/-!
# Source deductions for the marked G₂ pencil

`Assembly` constructs the line and point markings from the earlier local
orders, T-invariance and the Weyl L₁-commutator identity. It derives the
needed derived Sylow witness from the actual source Sylow, then applies the
three-line pencil and residual calculations to the literal quotient
U/(V₁.subgroupOf U). This proves the conditional source deductions
14.7.55(1),(2),(3),(6) without a marking, transitivity or quotient-isomorphism
premise. The residual remains O²(C_H(V₂)) of the unquotiented centralizer.

`Offenders` proves full-actor recognition from the numerical model bounds
and transports all of B.4.6's best offenders. `QuotientOffenders` identifies
their family with the H-conjugates of the actual `fixingSubgroup` of that
quotient pencil span. No minimality restriction is added.

These conditional deductions retain the earlier local identities and the
actual natural/Weyl identification from qt-14-07-g2-exclusion. Clause (5)
also retains the precise B.4.6 inputs from qt-b-04-g2 and the clause-(4)
centralizer input from qt-14-07-g2-pencil-centralizers. Their discharge and
the remaining clauses of 14.7.55 belong to qt-14-07-g2-marked-pencil.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1066,
PDF p.1083, and B.4.6, printed pp.88–90.
-/
