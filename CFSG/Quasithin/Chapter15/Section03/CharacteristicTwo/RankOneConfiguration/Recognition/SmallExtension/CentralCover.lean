module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Embedding
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Assembly

/-!
# The centralizing small-extension branch

For Q = [O₂(L),L] and D = C_I(Y₊), the actual quotient I⁺ = I/C_I(L)
acts faithfully on L. A genuine equivariant model of Z(Q)/C_Z(Q)(L)
derives C_L(Q) ≤ O₂(L). In the branch D ≤ C_I(Q), the earlier checked
three-subgroup and square arguments give [D,L] ≤ Z(Q), elementary D⁺,
and trivial Frattini subgroup when Z(Q) is elementary.

Commutators then embed the actual D⁺ faithfully into crossed homomorphisms.
Their central coefficient kernel is retained and eliminated by perfectness.
The cocycles vanish on O₂(L), so they descend to the actual model quotient.
Restriction to the marked Y₊ is zero. A model's marked cocycle-detection
calculation therefore implies D⁺ = 1. The universal-dual-cover interpretation
and its orientation are explicit in `detectedOn_iff_universal_fixed`.

For binary SL₃, the exceptional cocycle's spare coordinate proves that a
cocycle fixed by the marked radical transvection is principal. The marked
plane rotation eliminates its principal part. This proves the required
extension calculation for both one and two natural summands. It does not
apply I.2.3 to a group absent from that lemma's list.

`centralizing_branch` assembles all five surviving marked configurations:
the A₆ and G₂(2)' blocks, and C.1.34(1)--(3). It constructs the faithful
coefficient models, proves the marked cocycle calculations, and concludes
D⁺ = 1 together with the centralizer, elementary and Frattini properties.
`centralizers_eq_of_marked_configuration` gives C_I(Y₊) = C_I(L), and
`centralizing_branch_false` applies the genuine V₁-normalizer conclusions
of 15.3.29 to exclude this branch. The earlier MS classification, its actual
module and V₂-parabolic markings, and the noncentral branch remain with the
parent source owner. No universal I.2.3 implication is needed for this route.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
p.1132 (PDF p.1149), proof of 15.3.31; C.1.13, C.1.31--34, B.4.8,
I.1.5--6, and I.2.3 (whose group list excludes L₃(2)).
-/
