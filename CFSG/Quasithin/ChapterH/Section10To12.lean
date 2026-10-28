module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import CFSG.Quasithin.ChapterH.Section10To12.OffenderReduction
public import CFSG.Quasithin.ChapterH.Section10To12.TripleJames
public import Theory.Representation.BinaryOffender.FixedSpaceSpanCorank
public import CFSG.Quasithin.ChapterE.Section04.MathieuBounds

/-!
# The small Mathieu modules in H.10–H.12

H.10.1 is the existing `Representation.BinaryOffender.fixedSpaceSpan`.
The theorem `corankFixedSpaceSpan_rank_sub_one` proves its identification
with the corank construction in E.3.30. The literal M₁₂ permutation heart,
the genuine triple-cover input, and the quadratic offender reduction are
provided by the section's submodules. The complete E.4.3 Mathieu bounds
are re-exported with their genuine central-cover and outer-extension inputs.

H.12.1(1) is proved for every genuine triple cover: the faithful irreducible
binary module of dimension twelve exists and is unique up to an actual
representation equivalence. The proof's minimum-degree bound and the central
scalar action are also provided. The remaining module recognition, local
stabilizer and fixed-space calculations in H.11.1 and H.12.1(2–13) remain
source obligations. In particular the offender reduction alone is not a
proof that these modules have no offenders.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.10–H.12,
printed pp.392–394. H.11's rank-four assertion is used as an upper bound
in Table 7.2.1: the proof distinguishes rank three for M₁₂ from rank four
for its full automorphism group. H.12.1(3)'s proof uses the displacement
of U in its small-displacement hypothesis, although the statement prints V.
-/
