module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Assembly

/-!
# B.5.8: Fitting-centralization reduction

The complete universal B.1.9 input is specified in `FittingReduction.EarlierB19`.
A noncentral minimal offender supplies its actual nontrivial Fitting commutator.
`Configuration.adequate` proves the remainder of B.5.8 once B.1.9 has selected
its S₃ factor and the SQTK cover supplies the complementary rank bound. It
constructs the S₃ alternative when the second factor is trivial; otherwise it
classifies the strictly smaller second action, uses rank-one extraction and
transports every factor clause to the literal global fixed quotient.

`minimalBestOffender_centralizes_fitting_of_source` now assembles B.5.8 from
those proved reductions. It derives the actual configuration and cover-rank
bound, and supplies rank-one module extraction from B.4.8(3). The source
application `exceptional_configuration_of_source_counterexample` feeds this
centralization into the component recursion and constructs the exceptional
configuration remaining after B.5.12. No selected-factor, rank or extraction
assertion is an additional input of either result.

Earlier-source inventory: full B.1.9 (`qt-b01-fitting-structure`) and exact
A.1.31(1) (`qt-a-01-section-rank`), and B.4.8(3)
(`qt-b-04-natural-extensions`). The source assembly instantiates the former
intermediate `RankOneModuleExtraction` parameter with its proved producer.
The strong-induction owner `qt-b05-general-source-induction` retains the
strictly smaller-order induction hypothesis and the remaining final cases.
Universal earlier-source discharge belongs to `qt-b05-general-classification`.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.9, pp.71–72,
A.1.31, pp.27–28, and B.5.8, p.106.
-/
