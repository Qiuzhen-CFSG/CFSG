module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.PairingObstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.HomImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.NontrivialAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.Source

/-!
# The commutator route to the natural moving quotient in MS93

`CommutatorHom` constructs Φ on the actual unquotiented X, descending only
its second argument through hat W/hat V. It proves additivity, the exact
kernel criterion and equivariance with the original source marking. The
actual target is Z_a/(Z_a ∩ Z(G_a)), with its proved natural coordinates.

`Singer` and `HomImage` show that trivial local action on X/hat W would
force Φ(X)=Φ(hat W) and X=hat W · ker Φ. The image quotient has precisely
this product as its relative kernel; no vanishing of Φ(hat W) is used.
`NontrivialAction` supplies a source substitute for excluding trivial action:
the earlier centrality and the critical window force [X,Ltilde_a] not to
lie in hat W. This uses only the literal earlier (4.5.3)(i) equality. Simplicity then
gives C_Ga(X/hat W) ≤ Q_a. The reverse containment remains unproved.

The natural moving-section witness is still unproved. Its actual action
descent through source.projection, small-displacement recognition, natural
orientation and second-factor independence remain to be constructed.
The applications of dual_section_of_moving_section and
commutator_layers_of_moving_section therefore remain conditional. The
previous checked obstruction to the printed bilinear pairing is retained;
no counterexample to the full ambient MS93 theorem is claimed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(vii), p.895,
and (4.5.4)(iv) and its proof, pp.898--899.
-/
