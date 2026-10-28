module

public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Automorphisms
public import CFSG.Quasithin.ChapterA.Section01.Fitting.ReducedBounds
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Nilpotence
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Product
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Reduced

/-!
# Generalized Fitting results for §A.1

This module collects the source-facing generalized-Fitting results from
Aschbacher–Smith, *The Classification of Quasithin Groups*, printed pp.20–24.
Residual centralization of prime cores gives the solvable nilpotence criterion
A.1.4. The characteristic-p equivalence proves the generalized-Fitting form
of A.1.6 and the central-quotient theorem A.1.8; the automorphism argument
proves A.1.9 and its odd-core application. Component and odd-prime-core
exclusion prove the normal-product criterion A.1.10.

The reduced-two subgroup is the product of the normal elementary abelian
subgroups whose actual centralizer quotients have trivial two-core, as in
B.2.11–12, printed pp.77–78. Normal closure proves its Sylow-overgroup
inheritance in A.1.11. For A.1.19, the Thompson fixed-point kernel bound
constructs a reduced detecting witness inside the given elementary abelian
witness, yielding the full centralizer equality.
-/
