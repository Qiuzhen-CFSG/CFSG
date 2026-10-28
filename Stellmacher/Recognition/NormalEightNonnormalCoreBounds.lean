module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightNonnormalWidthOne
public import Stellmacher.Recognition.NormalEightNonnormalCyclicTail
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTail

/-!
# Order and index of the nonnormal quotient core

Under absence of normal elementary eights, the quotient two-core has order
sixteen and relative index two in the quotient Sylow subgroup. Intrinsic width
one and the ambient cyclic and noncyclic tail exclusions discharge the three
premises of the structural order/index reduction. All elementary bounds used
here retain their normality hypotheses.

Source: Janko–Thompson (1970), §4, printed pp.389–393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The nonnormal four image forces the quotient two-core to have order sixteen
and relative index two, assuming only the absence of normal elementary eights. -/
public theorem omegaQuotient_pCore_order_index
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : Stellmacher.IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  have hwidth := omegaQuotient_pCore_width_one
    hns hN S A hA hnonab hZ hno W hW hunique hnormal
  apply omegaQuotient_pCore_order_index_of_width_and_tail_bounds
    hN S hZ W hW hno hunique hnormal hwidth
  · intro B D hBn hDn hB hBc hD hc hg
    let : B.Normal := hBn
    let : D.Normal := hDn
    let : IsExtraspecial 2 B := hB
    let : IsCyclic D := hD
    exact omegaQuotient_cyclic_tail_card_lt_eight
      hns hN S A hA hnonab hZ W hW hno hunique hnormal B D hBc hc hg hwidth
  · intro B D hBn hDn hB hBc hD hn hc hg
    let : B.Normal := hBn
    let : D.Normal := hDn
    let : IsExtraspecial 2 B := hB
    exact omegaQuotient_noncyclicHallTail_card_lt_sixteen
      hns hN S A hA hnonab hZ hno W hW hunique hnormal hwidth B D hBc hD hn hc hg

end Stellmacher.Recognition.NormalEightNonnormalImage
