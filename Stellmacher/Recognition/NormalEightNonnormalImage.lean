module

public import Stellmacher.Recognition.NormalEightNonnormalSetup
public import ABG.ChapterII.Section1.WreathedElementaryRank
public import Stellmacher.Recognition.NormalEightNonnormalCoreBounds
public import Stellmacher.Recognition.NormalEightNonnormalTerminal

/-!
# Exclusion of the nonnormal quotient-image branch

The normal-only quotient setup is in `NormalEightNonnormalSetup`. A two-core
of order sixteen and relative index two give a Sylow subgroup of order
thirty-two. The wreathed conclusion of Janko–Thompson (1970), §4, p.393,
then contradicts the supplied elementary subgroup of order at least eight,
using the proved elementary-rank bound for wreathed groups.

The core bounds and the terminal ambient contradiction are proved in
`NormalEightNonnormalCoreBounds` and `NormalEightNonnormalTerminal`.
Their assembly here uses only the absence of normal elementary eights;
the supplied elementary subgroup of order at least eight need not be normal.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The core order and relative Sylow index give the original Sylow order. -/
public theorem card_sylow_eq_thirty_two (S : Sylow 2 G)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2) :
    Nat.card S = 32 := by
  have hcard := (omegaCorePreimage S).card_mul_index
  rw [card_omegaCorePreimage, index_omegaCorePreimage, hcore, hindex] at hcard
  exact hcard.symm

/-- The source's wreathed conclusion contradicts an elementary eight in the Sylow. -/
public theorem false_of_wreathed (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hw : ABG.IsWreathedOfHeight S 2) : False := by
  have hbound := ABG.elementary_card_le_four_of_isWreathedOfHeight hw A
  omega

/-- In a nonsolvable simple N₂-group, the nonnormal quotient image of the
unique normal elementary four is incompatible with the absence of normal
elementary eights when the Sylow subgroup contains an elementary eight. -/
public theorem false_of_nonnormal_image
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : Stellmacher.IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal) :
    False := by
  obtain ⟨hcore, hindex⟩ := omegaQuotient_pCore_order_index
    hns hN S A hA hnonab hZ hno W hW hunique hnormal
  have hS := card_sylow_eq_thirty_two S hcore hindex
  exact NormalEightNonnormalTerminal.false_of_terminal
    hns hN S hS A hA hnonab hZ W hW hno hunique hnormal hcore hindex

end Stellmacher.Recognition.NormalEightNonnormalImage
