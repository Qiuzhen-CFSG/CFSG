module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Quotient
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection

/-!
# Odd-core obstruction: quotient preparation and remaining assembly

The quotient C_G(A)/(O(C_G(A)) A) is constructed with its actual normal
kernel. For A ≤ U ≤ V, its U-image has cardinality [U : A], and failure of
odd-core containment gives a nontrivial odd core in its centralizer.
The quotient itself has trivial odd core. E.6.5 supplies the original and
quotient Sylow subgroups, with the image of V central in each.

To finish `OddCoreObstruction`, two obligations remain: construct the
`DetectedComponent` using Aschbacher 31.14(1), 31.18 and a justified lift to
an ordinary component; then inspect the genuine E.6.8 alternatives to
identify that component as A7 or its perfect central three-cover. This
module does not yet assert the obstruction theorem or the balance theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263); E.6.8, printed pp.247–248 (PDF pp.258–259).
-/
