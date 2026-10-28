module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.HermitianDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.CoverComparison
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceImage

/-!
# K.3.2 recognition: concrete tensor descent and source-image transport

The scalar extension of the descended Hermitian space is proved equivalent
to the literal twisted natural tensor. An equivalence of inflated binary
actions identifies the exact covering kernels and yields a compatible action
equivalence with the faithful image, distinguishing PSL₃ from SL₃. The original
ambient group's image satisfies Chapter H's solvable-residual equation by a
proof from F*(G) and the actual PSL₃ central quotient. Its allowed diagonal and
coefficient actions follow from the checked normalizer theorem.

The exhaustive K.3.2 catalogue still needs the cubic-bound module sieve:
for SL₃, exclude the at-least-8r branch of the existing absolute catalogue;
for SL₄(2) and SL₅(2), force the small-degree ranges to which the existing
recognition theorems apply. Those bounds are not asserted or assumed to be
recognition results here. Final module-list assembly remains in this module's
owning task; the offender calculations belong to the Linear family owner.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, K.3.2,
printed pp.454–456, citing GM04 Proposition 4.6 and Table 7.
-/
