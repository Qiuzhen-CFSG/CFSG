module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.NormalizerControl
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.PrimeSupport
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.SylowGeneration
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoreObstruction

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.ConjugateGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.ProductConsequences
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.LocalQuotients

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoordinateLifting
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.Assembly

/-!
# Local relations for the terminal amalgam

The earlier Baumann control gives both ambient normalizer bounds, and
the earlier core/Thompson identities give relative Thompson normality
in the first local group. The genuine earlier quotients supply prime
support. Compatible conjugation constructs a distinct singular four-group
`F=Eˢ` containing the actual central involutions of `T`.

The normal cubic residual and its Thompson commutator identify the second
local group's intrinsic quotient with `S₃`. Product cardinalities in the
original line normalizer prove `G₁ ∩ G₂=T_E`, without comparing the two
local cores. The literal product `Y=Y_E Y_F O₂(Y)` gives `⟨Y_F,T⟩=M`;
together with `N_M(T_E)≤T`, this supplies the generation premise in
`Sylow.lean`. The orthogonal product and normalizer calculations are
proved for the specified compatible action. `exists_terminal_local_relations`
assembles all these relations, including maximal-local Sylow promotion,
from the genuine earlier conclusions of 15.3.2, 15.3.7 and 15.3.66–67.

`CoreObstruction` preserves the refutation of the printed equality
`O₂(G₁) ∩ O₂(G₂)=C_T(V)` under 15.3.67(3),(4). No replacement common-core
condition is used. The parent owns the separate centrality argument for
`O₂(G₀)` and the final assembly of Lemma 15.3.68.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1155, PDF pp.1169–1172.
-/
