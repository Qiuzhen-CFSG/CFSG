module

public import Stellmacher.Recognition.NormalEightQuaternionAbelianSetup
public import Stellmacher.Recognition.NormalEightQuaternionCyclicFour
public import Stellmacher.Recognition.NormalEightQuaternionFourElementary
public import Stellmacher.Recognition.NormalEightQuaternionFourNonElementary

/-!
# Assembly for the quaternion-core abelian quotient branches

The cyclic-four branch reduces to a locally fully centralized outside
involution. The elementary-four branch additionally splits according to whether
its fixed core is elementary. Both exclusions are required: an arbitrary
elementary eight or sixteen does not contradict the normal-only rank bound.

The assembly preserves the outside conjugacy witness while selecting its
centralizer, then applies the proved branch-specific characteristic-line and
transfer exclusions. The final two theorems require no saturation or fixed-core
hypothesis on the supplied outside conjugate.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, cases (a), (b)(i), (b)(ii),
printed p.391.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- It suffices to exclude locally fully centralized outside conjugates. -/
public theorem quaternion_abelian_false_of_saturated_exclusion
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hx : x ∉ omegaCorePreimage S) (hzx : IsConj (z : G) (x : G))
    (hexclude : ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
      IsConj (z : G) (t : G) →
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) → False) :
    False := by
  obtain ⟨t, ht, hout, hconj, _, hsat⟩ :=
    exists_outside_isConj_with_saturated_common_centralizer S hZ z x hz hzc hx hzx
  exact hexclude t ht hout hconj hsat

/-- The four-group quotient requires both elementary and non-elementary
fixed-core exclusions for the selected outside conjugate. -/
public theorem quaternion_four_false_of_saturated_fixed_core_exclusions
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hx : x ∉ omegaCorePreimage S) (hzx : IsConj (z : G) (x : G))
    (helementary : ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
      IsConj (z : G) (t : G) →
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) →
      IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
        (centralizer ({t} : Set S))) → False)
    (hnonelementary : ∀ t : S, orderOf t = 2 → t ∉ omegaCorePreimage S →
      IsConj (z : G) (t : G) →
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) →
      ¬ IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
        (centralizer ({t} : Set S))) → False) : False := by
  apply quaternion_abelian_false_of_saturated_exclusion S hZ z x hz hzc hx hzx
  intro t ht hout hconj hsat
  by_cases he : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S)))
  · exact helementary t ht hout hconj hsat he
  · exact hnonelementary t ht hout hconj hsat he

/-- A cyclic-four quotient of the quaternion core is incompatible with the
supplied outside fusion. Local saturation is obtained by conjugate selection. -/
public theorem quaternion_cyclic_four_quotient_false
    [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (_ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G))
    (hindex : (omegaCorePreimage S).index = 4)
    (hcyclic : IsCyclic (S ⧸ omegaCorePreimage S)) : False := by
  apply quaternion_abelian_false_of_saturated_exclusion S hZ z t hz hzc hout hconj
  intro u hu huout hzu hsat
  exact quaternion_cyclic_four_false hns hN S A hA hnonab hZ hno W hW hunique
    hnormal hH B C hB hC hjoin hinter hcomm z u hz hzc hu huout hzu hindex hcyclic hsat

/-- A four-group quotient of the quaternion core is incompatible with the
supplied outside fusion, in both the elementary and non-elementary fixed-core
cases. No bound on arbitrary elementary subgroups is assumed. -/
public theorem quaternion_four_quotient_false
    [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (_ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G))
    (hindex : (omegaCorePreimage S).index = 4)
    (hquot : IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S)) : False := by
  apply quaternion_four_false_of_saturated_fixed_core_exclusions S hZ z t hz hzc hout hconj
  · intro u hu huout hzu hsat hfixed
    exact quaternion_four_elementary_false hns hN S A hA hnonab hZ hno W hW hunique
      hnormal hH B C hB hC hjoin hinter hcomm z u hz hzc hu huout hzu hindex hquot
      hfixed hsat
  · intro u hu huout hzu hsat hfixed
    exact quaternion_four_false_of_non_elementary_fixed_core hN S hZ hno W hW hH
      B C hB hC hjoin hinter hcomm z u hz hzc hu huout hzu hquot hfixed hsat

end Stellmacher.Recognition.NormalEightNonnormalImage
