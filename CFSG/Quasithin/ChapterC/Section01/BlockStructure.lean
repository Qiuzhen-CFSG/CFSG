module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer

/-!
# Structure of short groups and blocks

This entry point proves C.1.8, the intrinsic layer centralizer, and the
single-block case of C.1.11. It also proves the final group-theoretic step
of C.1.10 with fixation of U explicit, and defines its actual endomorphism
field and prime set, including the empty-set convention.

Full C.1.9, the field-action step of C.1.10, and the arbitrary-product
structure needed by C.1.11 remain separate obligations. They are not
included in the short-group or block hypotheses.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.8--C.1.11, printed pp.123--124.
-/
