module

public import Stellmacher.Recognition.NormalEightQuaternionFourElementarySetup
public import Stellmacher.Recognition.NormalEightQuaternionFourElementaryReduction
public import Stellmacher.Recognition.NormalEightQuaternionFourElementarySixteen

/-!
# Assembly of the elementary quaternion fixed-core exclusion

The elementary fixed core has order at most four by the normality argument
in the setup module. The outstanding transfer reduction must identify that
fixed core with the distinguished four and reduce the Sylow centralizer to
an elementary group of order sixteen, with every involution conjugate into
the distinguished four. The final second-involution argument then excludes
this remaining centralizer. The theorem below keeps these two mathematical
obligations explicit and assembles them with the proved fixed-core bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (b)(ii), printed p.391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage

/-- The elementary branch reduces to the transfer reduction and the final
order-sixteen centralizer argument. The fixed-eight obstruction is discharged. -/
public theorem quaternion_four_elementary_false_of_reduction
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    [IsMulCommutative (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (W : Subgroup S) (t : S) (ht : t ^ 2 = 1)
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))))
    (hreduce : Nat.card ((omegaCorePreimage S).subgroupOf
        (centralizer ({t} : Set S))) ≤ 4 →
      omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W ∧
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) ∧
      Nat.card (centralizer ({t} : Set S)) = 16 ∧
      ∀ u : S, orderOf u = 2 → ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G))
    (hexclude : omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W →
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) →
      Nat.card (centralizer ({t} : Set S)) = 16 →
      (∀ u : S, orderOf u = 2 → ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G)) → False) :
    False := by
  obtain ⟨hW, hE, hcard, hcover⟩ := hreduce
    (omegaCorePreimage_elementary_fixed_card_le_four
      S hno hH B C hB hC hjoin hinter hcomm t ht hfixed)
  exact hexclude hW hE hcard hcover

/-! The elementary fixed-core branch with the full recognition interface. -/
public theorem quaternion_four_elementary_false
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧
      8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (_hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center S)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G))
    (hindex : (omegaCorePreimage S).index = 4)
    (hquot : IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S))
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (Subgroup.centralizer ({t} : Set S))))
    (hsat : ∀ V : Subgroup G, IsPGroup 2 V →
      (Subgroup.centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ Subgroup.centralizer ({(z : G), (t : G)} : Set G) →
      V = (Subgroup.centralizer ({t} : Set S)).map (S : Subgroup G).subtype) :
    False := by
  let : IsMulCommutative (S ⧸ omegaCorePreimage S) := hquot.toIsMulCommutative
  apply quaternion_four_elementary_false_of_reduction S hno hH B C hB hC hjoin hinter hcomm
    W t (by simpa only [ht] using pow_orderOf_eq_one t)
    hfixed
  · intro hfixed_card
    exact quaternion_four_elementary_reduction _hns hN S A _hA _hnonab hZ hno W hW
      hunique _hnormal hH B C hB hC hjoin hinter hcomm z t hz hzc ht hout hconj hindex
      hquot hfixed hfixed_card hsat
  · intro hfixedW hEelem hEcard hcover
    exact quaternion_four_false_of_elementary_sixteen_and_cover hN S hZ hno W hW hH B C
      hB hC hjoin hinter hcomm z t hz hzc ht hout hindex hquot hfixedW hEelem hEcard hcover

end Stellmacher.Recognition.NormalEightNonnormalImage
