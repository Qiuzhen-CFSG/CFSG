module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3Four.FieldExtension.PairedAction
public import Theory.SpecificGroups.PSL3Four.FieldExtension.SemilinearInclusion

/-!
# PSL(3,4) extended by its field automorphism

This module assembles the concrete semidirect product `PSL(3,4) ⋊ C₂`, its
faithful paired action on projective points and line covectors, and its natural
index-three inclusion into `PΓL(3,4) = PGL(3,4) ⋊ C₂`.

`Basic` constructs entrywise Frobenius, the split field projection and its
linear kernel, and proves the orders 20160 and 40320. `PairedAction` descends
the matrix action on points and the inverse-transpose action on line covectors;
the field involution squares coordinates on both. Its faithfulness follows
because coordinate Frobenius cannot be induced by a linear matrix.
`SemilinearInclusion` extends the natural inclusion of PSL into PGL, proves
the full semilinear group has order 120960, and obtains index three by counting.

All constructions and formulas are re-exported in namespace `Matrix.PSL3Four`.

Source: Aschbacher, *Sporadic Groups*, §18, especially 18.7–18.9;
quasithin Lemma 5.2.18(1).
-/
