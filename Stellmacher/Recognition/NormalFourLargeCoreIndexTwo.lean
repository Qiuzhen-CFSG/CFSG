module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourLargeCoreIndexTwoFusion

/-!
# Excluding the index-two large core

The actual quotient is the literal central-omega quotient
`N_G(Ω₁(Z(S)))/O₂′`.  The preceding fusion module proves that an
extraspecial two-core of order thirty-two cannot have relative Sylow index two
under the ambient elementary-rank bound.  This file supplies the
normal-four-facing statement and translates the index of the core preimage in
the original Sylow into that relative index.

Source: Janko--Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

/-- The index-two extraspecial large-core branch is impossible in the
normal-four setup.  The normal-four data are retained at this interface so
that the theorem can be used directly by the nonnormal-image assembly. -/
public theorem normal_four_large_core_index_two_false
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (_hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G)
    (_hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (_hE : Nat.card E = 4)
    (_hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (_hnormal : ¬ (fourImage S E).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) :
    False := by
  have hindex' : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 :=
    (index_omegaCorePreimage S).symm.trans hindex
  exact large_core_index_two_false hns hrank S hH hindex'

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
