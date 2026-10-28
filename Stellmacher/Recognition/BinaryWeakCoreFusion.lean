module

public import Stellmacher.Recognition.BinaryCentralizerFusion
public import Theory.GroupTheory.BinaryWeakCoreFusion

/-!
# Binary weak-core component transport

Let G be a finite nonsolvable simple N₂ group and S a Sylow two-subgroup.
Suppose A ≤ S is elementary of order at least eight, Q ≤ S contains an
elementary four-group, and Q C_S(Q) contains an elementary subgroup B of
order at least eight. Then every element of N_G(Q) preserves the elementary
commuting component of A.

Binary centralizer fusion controls C_G(Q). The general Frattini reduction
chooses a Sylow subgroup of Q C_G(Q) containing B, controls its normalizer
through the common rank-three vertex B, and concludes the normalizer claim.
The source-neutral reduction stays in Theory; the N₂-group application is
assembled here.

Source: the binary simple-group remark following GLS2, Proposition 22.4(i),
`refs/KGroup/GLS2/ChapterF.tex`.
-/

namespace Stellmacher.Recognition
open Subgroup

/-- Exact binary weak-core transport under the original rank hypotheses. -/
public theorem binaryWeakCore_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q E B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) (hQS : Q ≤ S)
    (hEQ : E ≤ Q) (hE : 4 ≤ Nat.card E)
    (hBQC : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (hB : 8 ≤ Nat.card B)
    (g : G) (hg : g ∈ normalizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj g).toMonoidHom) := by
  exact elementaryCommutingConnected_conj_of_centralizer_transport
    (S : Subgroup G) A Q B S.isPGroup' hA hB hAS hQS
    (hBQC.trans (sup_le hQS inf_le_left))
    (hBQC.trans (sup_le_sup_left inf_le_right Q))
    (binaryCentralizer_transport hG hN S A Q E B hAS hA hQS hEQ hE hBQC hB) g hg

end Stellmacher.Recognition
