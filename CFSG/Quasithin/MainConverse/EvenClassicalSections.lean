module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThreeBinary
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.BinaryDerived

/-!
# Proper simple sections of the even classical alternatives

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Main
Hypothesis 0.1.1(K) and Theorem 0.1.2(1–2), printed p.4, repeated on p.482.
The carriers and parameters are those of `ClassicalModels.lean` and
`ClassificationModels/Families.lean`.

The binary PSL₃ endpoint and the actual commutator PSp₄(2)′ are proved.
Their proper simple sections are respectively prime cyclic, and prime
cyclic or A₅. Both results give actual carrier equivalences and quotient
formulations with relative normality. The K corollaries assume only
inclusion of finite simple constructed carriers in the full catalogue.

The remaining calculations are PSL₃(2^f) for f ≥ 2, PSL₄(2), PSL₅(2),
PSU₄(2^f) for f ≥ 1, PSU₅(4), PSp₄(2^f) for f ≥ 2, and PSp₆(2).
Unitary parameters refer to fixed-field order, so PSU₅(4) uses a field of
order sixteen. This module does not yet assert their combined proper-K
clause. The QT and E calculations are independent of these section proofs.
-/
