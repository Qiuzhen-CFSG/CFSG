module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Blocks
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.StarQuotient
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TransferObstruction
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceConclusions
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceElimination

/-!
# The locally normal branch of §13.5

For the ordinary A₆ case, `SourceConclusions.source13_5_15` constructs all
nine conclusions from the original natural datum, F.9 hypothesis, seed
identity, nonabelian U_H and normality of L₁ in H. It selects the original
pair internally and proves the required maximality through the earlier
upper-component exclusion. No completed local conclusion is an input.

When M=L, the original returning plane and the Asc94 type recognition
then give the actual U₄(3) model. This is exported as
`SourceConclusions.modelConclusion_of_local_eq`.

`SourceElimination.original_normal_a6_false` closes the remaining S₆
extension by actual weak closure, involution fusion, transfer and the
cubic norm Frattini contradiction. It uses the original natural datum,
F.9 hypothesis, ordinary A₆ quotient and seed identity. Its universal
nonnormality consequence supplies the missing normal-branch input to
13.5.19; only the earlier F.9 family and ambient geometry remain there.

The ordinary A₅ branch of 13.5.17 and the preceding reductions selecting
the ordinary local model are separate source steps.
The earlier marked interfaces and the nine-field conclusion structure
remain available unchanged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.15–17, printed pp.919–922 (PDF pp.936–939).
-/
