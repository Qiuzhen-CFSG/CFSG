module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Assembly

/-!
# Binary commutator pairings for original MS93 (1.7)

`Source` specifies the actual marked extension and local residuals, retaining
(A), the common Sylow choice, normality of X_alpha in the actual local
normalizer M_alpha, and the natural local quotient. It proves
that the normal closure is a two-group and that the fixed preimage is normal
in it, making the source barred quotient well-defined.

`Generic` constructs the literal commutator pairing and identifies its kernel
with C_U(W). The evaluation quotient isomorphism is equivariant under L when
[W,L,U] = 1; it does not require L to centralize W elementwise. Irreducibility
then turns nonzero evaluations into surjections and gives [U,w] = Z.

`Assembly` exports `theorem_1_7_i` and `theorem_1_7_ii` in the
`RankOnePairing` namespace. They prove
both source clauses from `SourceData`, discharging the local-structure and
incidence premises. Case (ii) retains the source's additional natural-factor
hypothesis. `SourceData.fixedQuotientEquiv` constructs the actual equivariant
isomorphism in case (i); `SourceData.dualFactor` constructs compatible
inverse-transpose coordinates in case (ii).

Source: Meierfrankenfeld--Stellmacher (1993), pp.828--829,832,847--848.
-/
