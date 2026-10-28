module

public import CFSG.Quasithin.ChapterF.Section02.UniversalAutomorphisms.Existence
public import CFSG.Quasithin.ChapterF.Section02.UniversalAutomorphisms.FaithfulConjugation

/-!
# Universal completions and their automorphisms

This is the assembled interface for Aschbacher--Smith, *The Classification of
Quasithin Groups*, §F.2.1--F.2.10 (printed pp. 264--268).

`UniversalCompletion.universalCompletion A` constructs the universal group from
vertex generators and the multiplication and diagram relations. It supplies the
universal-completion input to `piHat`, `kernelStabilizer`, and `piMinus`; no
existence hypothesis is needed. The carrier lies in `Type (max u v)`, and the
existing universal-completion interface uses that same universe for targets.

Descent is defined on the quotient by the completion kernel and transported by
the first isomorphism theorem. `piMinus_map` evaluates it on every vertex image,
and `piMinus_mul` gives its homomorphism law. For faithful completions,
`faithfulStabilizerEquiv` identifies this representation with restriction of
automorphisms preserving every vertex image.

For nested subgroup amalgams, `YAmalgam.NormalIn.conjugation` constructs the
least-vertex conjugation action. Its kernel, universal action, stabilization of
each completion class, and descended inner action are given by
`conjugation_ker`, `piHat_innerConjugation`,
`innerConjugation_act_equivalent`, and `piMinus_innerConjugation`.
-/
