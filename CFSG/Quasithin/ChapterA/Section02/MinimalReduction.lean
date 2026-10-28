module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Kernel
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Cases
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ProperSections

/-!
# Minimal-counterexample reductions for Theorem A

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.8–15, printed pp.34–38.

The imported proofs establish minimal covering and its normal quotient
(A.2.8–9), vanishing two-core (A.2.10), the two rank obstructions in A.2.14,
and every assertion of proper-section control in A.2.15. They also establish
perfectness and nonsimplicity of the A-counterexample, and centrality of its
kernel once quasisimplicity is available. Every induction premise is the
explicit proper-section hypothesis from `Statements`.

A.2.11's prime-core identification, A.2.12's nonsemisimple and component-product
arguments, and the remaining Case I/II assembly in A.2.13 are not yet proved
here. In particular the prime-center clause of A.2.14 retains quasisimplicity
as the source Case II hypothesis; it does not prove A.2.12.
-/
