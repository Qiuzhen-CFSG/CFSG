module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.RecognitionInputs
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.TripleCover
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Assembly

/-!
# Cubic centralizer deductions for J.2.7

The opening stage proves clauses (2),(9): the literal C_G(B)/B is the
specified M₁₀, its two-residual maps to the actual inner A₆, and all
involutions of C_G(B) are ambient-conjugate to z. It takes the marked
J.2.5 witness, J.2.6, generator fusion in H, and exactly I.4.1(2).

The later stage proves clauses (1),(11) from the intervening Aut(A₆)
normalizer marking and transposition part of (7). It excludes E₂₇,
constructs an extraspecial ambient Sylow of order 27 and exponent three,
and identifies L_B=C_G(B)^∞ with the concrete hexacode triple cover by an
equivalence commuting with the quotient map to A₆. The kernel is precisely
the original B, and order-three fusion retains actual ambient conjugators.

The parent source assembly retains discharge of all earlier witnesses,
I.4.1 and clauses (3),(7). These conditional stages are separate so the
normalizer construction can use the opening quotient recognition.

Source: Aschbacher–Smith, J.2.7, printed pp.435–437 (PDF pp.446–448).
-/
