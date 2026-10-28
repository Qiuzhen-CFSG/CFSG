module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Defs
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.CoreConsequence
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.TernaryLine
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.AffineModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic.OmegaEndgame
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic.SourceAssembly

/-!
# The centralizer reduction in Section 15.4

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp. 1155–1161.

The imported theorem proves the implication from 15.4.8 to 15.4.11(1):
`C_G(Z) = T` implies `C_M(⟨Z^M⟩) = O₂(M)` for every overgroup `M` of `T`.
Inside `M`, the centralizer of `Z` is its Sylow subgroup `T`. The centralizer
of its normal closure is therefore exactly the two-core. This argument
needs neither solvability nor the representation-theoretic reductions.

The normal cubic witness step in 15.4.9 is also proved from the preceding
solvability, prime-divisor, three-rank and uppercase-Ξ exclusion reductions.
The proof constructs the omega-center of the three-core in the centralizer
quotient. Its order is three or nine; in the nine case, the Ξ exclusion
supplies an invariant cubic subgroup. The action on the four cubic subgroups
then constructs a normal cubic subgroup, whose residual preimage belongs to
the original family `NormalCentralizerXi`. The earlier source reductions and
the action control in 15.4.10 remain with the source assembly.

The affine-nine representation step in 15.4.10 is now proved for both natural
semidirect products. Its consumer pulls back the original action of H/C_H(W)
on W=⟨Z^H⟩ through the source model isomorphism and contradicts genuine
15.4.2(4). The preceding source reductions still supply the model and the
applicability conditions of that earlier bound.

The later normal-closure argument now constructs its complementary cubic
subgroup by the same four-point method. Its residual lift belongs to the
original family, and the two factors generate the actual normal closure.
Applying 15.4.10 to both factors puts that closure normally in the second
action centralizer. The two literal images are identified through the
intrinsic quotient by the two-core. The second image is the first omega
subgroup of the three-core of that action centralizer's image, so the normal
closure is normal in both maximal two-local overgroups. Their common
normalizer of its nontrivial two-core then forces the overgroups to coincide.
The source assembly also constructs the first elementary-nine image and
chooses a member nonnormal in one of the two overgroups. It therefore proves
the centralizer equality from the genuine preceding 15.4.5 cubic-quotient,
15.4.9 existence and 15.4.10 action-control results, together with the original
local rank and characteristic-two hypotheses.

The proof of 15.4.8 from Hypothesis 15.4.1, the exceptional alternative
in 15.4.7, and the construction and structure of the family `Y` remain
to be assembled from the earlier local and module results. In particular,
the centralizer equality below is an explicit intermediate input, not an
additional hypothesis of the intended final theorem.
-/
