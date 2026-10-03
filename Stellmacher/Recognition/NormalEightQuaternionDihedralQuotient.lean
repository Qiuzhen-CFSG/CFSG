module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightQuaternionDihedralGeometry
public import Stellmacher.Recognition.NormalEightQuaternionDihedralFusion
public import Theory.GroupTheory.SaturatedInvolutionSquareFusion

/-!
# Transfer in the dihedral-eight quotient branch

For the actual Sylow core preimage, the dihedral case reduces to two inputs.
The local quaternion action supplies an index-two subgroup whose outside-core
involutions are squares, and an involution with nonabelian fixed core of order
eight. Such an involution lies outside that index-two subgroup. Ambient fusion
control supplies another involution of this kind whose Sylow centralizer is
saturated and whose class misses the core.

Thompson transfer puts this class into the index-two subgroup. Its target is
outside the core, so is a square. Saturation transports a square root back,
contradicting the fact that every square lies in the index-two subgroup.
This module proves the final implication; construction of the local action
and fusion-control inputs remains separate. No bound on arbitrary elementary
subgroups is imposed.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392,
using the quaternion action calculations on pp.390–391.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The local action calculation and the ambient centralizer calculation
suffice for the dihedral quotient contradiction. The latter only needs to
supply a saturated representative with the same nonabelian fixed-core type. -/
public theorem quaternion_dihedral_false_of_geometry_and_fusion [IsSimpleGroup G]
    (S : Sylow 2 G) (W : Subgroup S) (hW : Nat.card W = 4)
    (hgeometry : ∃ M : Subgroup S, M.index = 2 ∧
      (∀ x : S, orderOf x = 2 →
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 →
        x ∉ M) ∧
      (∀ u : S, u ∈ M → u ∉ omegaCorePreimage S → orderOf u = 2 →
        ∃ r : S, r ^ 2 = u) ∧
      ∃ l : S, orderOf l = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8)
    (hfusion : ∀ l : S, orderOf l = 2 →
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) →
      Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 →
      ∃ x : S, orderOf x = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 ∧
        (∀ V : Subgroup G, IsPGroup 2 V →
          (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
          V ≤ centralizer ({(x : G)} : Set G) →
          V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) ∧
        ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G)) : False := by
  have hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
    intro K hK hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with hb | ht
    · have hbound : 4 ≤ Nat.card G := hW ▸
        W.card_le_card_group.trans (S : Subgroup G).card_le_card_group
      rw [hb, index_bot] at hi
      omega
    · simp [ht] at hi
  obtain ⟨M, hM, hout, hsquares, l, hl, hlnonab, hlcard⟩ := hgeometry
  obtain ⟨x, hx, hxnonab, hxcard, hmax, hcore⟩ := hfusion l hl hlnonab hlcard
  exact S.false_of_index_two_square_fusion hno (omegaCorePreimage S) M hM x hx
    (hout x hx hxnonab hxcard) hmax hcore hsquares

/-! The preceding local assembly is unconditional under the recognition
hypotheses: the quaternion action supplies the maximal subgroup and fixed
eight, while the characteristic-line and core-separation calculations supply
the saturated fusion representative. -/

public theorem quaternion_dihedral_false [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧
      8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (htP : t ∉ omegaCorePreimage S)
    (hzt : IsConj (z : G) (t : G))
    (hquot : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)) : False := by
  obtain ⟨M, hM, hout, hsquares, l, hl, hlnonab, hlcard⟩ :=
    quaternion_dihedral_geometry hns hN S A hA hnonab hZ hno W hW hunique hnormal
      hH hindex B C hB hC hjoin hinter hcomm z t hz hzc ht htP hzt hquot
  have hgeometry : ∃ M : Subgroup S, M.index = 2 ∧
      (∀ x : S, orderOf x = 2 →
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 →
        x ∉ M) ∧
      (∀ u : S, u ∈ M → u ∉ omegaCorePreimage S → orderOf u = 2 → ∃ r : S, r ^ 2 = u) ∧
      ∃ l : S, orderOf l = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 :=
    ⟨M, hM, hout, hsquares, l, hl, hlnonab, hlcard⟩
  have hfusion : ∀ l : S, orderOf l = 2 →
      ¬ IsMulCommutative
        (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) →
      Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 →
      ∃ x : S, orderOf x = 2 ∧
        ¬ IsMulCommutative
          (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 ∧
        (∀ V : Subgroup G, IsPGroup 2 V →
          (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
          V ≤ centralizer ({(x : G)} : Set G) →
          V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) ∧
        ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G) := by
    intro l hl hlnonab hlcard
    exact quaternion_dihedral_fusion hN S hZ hno W hW hH hquot B C hB hC hjoin
      hinter hcomm z hz hzc l hl hlnonab hlcard
  exact quaternion_dihedral_false_of_geometry_and_fusion S W hW hgeometry hfusion

end Stellmacher.Recognition.NormalEightNonnormalImage
