module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowIntersection
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import Theory.GroupTheory.ConjugateKernelObstruction

/-!
# Four-group transfer: source contracts and common arguments

The Sylow-center obstruction proves the common argument of 16.3.4 from
explicit model geometry. The conjugate-kernel obstruction proves the
maximal-centralizer intersection, elementary quotient, and order-four
contradiction in 16.3.6. Component restriction treats the cyclic order-four
possibility in 16.3.8.

The concrete model geometry, the exceptional alternatives of 16.3.5, and the
marked order-four lifts still have to be constructed. They are separate
prerequisites; the definitions in Contracts do not prove them. In particular
this module does not yet assert 16.3.6 or construct NonterminalCentralizerShape.
Final assembly, including the maximal choice and the normal four-subgroup
argument, remains in this module's owning task.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.4–16.3.8, printed pp.1178–1180 / PDF pp.1195–1197.
-/
