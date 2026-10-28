module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.DimensionRatio
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallRatio
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ParabolicConclusion
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.OuterActorElimination

/-!
# Native statement and reductions for the B.5.1 source implication

`QuasisimpleSourceConclusion` retains all six source clauses on the original
representation. `QuasisimpleSourceHypothesis.movedSection` constructs its
literal moved quotient from the original hypotheses. The quantitative
reduction proves dimension descent, the sum-of-ratios inequality, positivity,
the pairwise bounds, and the attained minimum at most the reciprocal of the
number of selected noncentral factors. The full earlier B.4.2 implication
then yields the natural rows for an irreducible constituent of ratio at most
one half.

`MovedSection.sylowFixedCentralizer_of_naturalDual` proves the full clause-(6)
implication on the original representation. Natural and dual first-cohomology
vanishing gives its fixed supplement, and the concrete Sylow centralizer
calculation transports all intrinsic and ambient subgroup maps. No additional
splitting or cohomology premise remains in this implication.

`whole_of_marked_outer_summands` gives G = L in case (II) once the induction
has constructed its faithful marked group action and disjoint natural socle
summands. It uses the proved full automorphism-centralizer rank bound, the
fixed diagonal, and the cyclic outer quotient to exclude exchanging offenders.

The complete B.5.1 implication is not yet proved here. In particular the
construction of the chief flag, induction establishing its natural factors,
socle and extension arguments, the marked hypotheses for outer elimination,
and clauses (2)--(5) are still required. The target predicate
`QuasisimpleClassificationInput` is never used as a proof premise.

Earlier-source parameter inventory for the current reductions:
* `IrreducibleClassificationInput` is the complete universal B.4.2 implication.
  Its hypotheses concern a finite SQTK group with quasisimple F*, a finite
  faithful binary representation irreducible on F*, and a best offender.
  The output is the full eleven-case action list, including offender clauses.
* B.1.5(8) is supplied by the proved `source_lemma_B_1_5_8`, not a parameter.
  Quadratic replacement and all flag inequalities likewise use proved APIs.
* The I.1.6(6) natural SL cohomology vanishing used for clause (6) is proved
  by `SLHigherNatural.H1_subsingleton_of_four_le`. The inverse-transpose
  intertwiner and product cocycle argument discharge the dual and sum cases.
* Both concrete model inputs (the Sylow-fixed centralizer and the full
  outer-involution centralizer rank) are now proved and used, not parameters.

The other permitted B/A/I source implications have not yet been added as
parameters. No unproved assertion about splitting or the desired action of
the current module is substituted for any of them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.5.1, printed pp.99–103. The unconditional source
assembly remains in `Section05.Quasisimple`.
-/
