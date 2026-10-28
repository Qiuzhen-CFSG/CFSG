module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.SpecificGroups.ExoticTwoGroup.Presentation

/-!
# Finite order reduction for the exotic extension

Given a normal self-centralizing C₄-square base in the Sylow two-subgroup,
conjugation bounds its index by the two-part of 96. The elementary sixteen
and the unique central involution exclude indices at most four. Thus the
remaining extension orders are 128, 256, and 512.

This is the intrinsic order reduction for Janko–Thompson, Math. Z. 113
(1970), 1.4(c), printed p.386, as used on p.395. Selecting the order-256
extension and constructing its six generators require further arguments;
no recognition assertion is made by the order bound.
-/

namespace Stellmacher.Recognition.NormalEightExoticExtension

open Subgroup

/-- An explicitly supplied C₄-square base reduces the extension problem to
three possible orders. The reduction itself needs no ambient fusion assumptions. -/
public theorem extension_order_cases
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set S) ≤ D)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    Nat.card S = 128 ∨ Nat.card S = 256 ∨ Nat.card S = 512 :=
  card_cases_of_selfCentralizing_c4_square S.isPGroup' D hDC hmodel
    (four_lt_index_of_normal_abelian_of_elementary_sixteen hZ hno B hB D)

end Stellmacher.Recognition.NormalEightExoticExtension
