module

public import Stellmacher.Recognition.NormalEightQuaternionAbelianSetup
public import Stellmacher.Recognition.NormalEightQuaternionCyclicFourOrbit
public import Theory.GroupTheory.PGroup.CyclicFourFixedCoreDerived
public import Theory.GroupTheory.PGroup.CyclicFourSectionDerived
public import Theory.GroupTheory.SaturatedCentralizerDerivedFusion

/-!
# The saturated cyclic-four quaternion-core exclusion

The quaternion square-action calculation gives a fixed elementary four and
one core orbit of involutions in the outside coset. Correcting conjugates by
core elements makes the involution centralizer cover the cyclic-four quotient.
Its fixed four is normal, hence the specified unique normal four.

A normal-subgroup-chain argument then shows that the centralizer has derived
subgroup equal to the central involution line. The supplied local saturation
excludes fusion with that central involution. The section-based interface is
retained, while the final theorem uses the intrinsic involution orbit directly.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (a), printed p.391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

/-- A normalized cyclic-four section completes the saturated quaternion-core
exclusion. The remaining input is the quaternion action's section geometry. -/
public theorem quaternion_cyclic_four_false_of_section
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (hconj : IsConj (z : G) (t : G))
    (hsat : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G), (t : G)} : Set G) →
      V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype)
    (K : Subgroup S) (Z : Subgroup K) [Z.Normal] [IsCyclic (K ⧸ Z)]
    (hquot : Nat.card (K ⧸ Z) = 4)
    (hZK : Z ≤ (center S).comap K.subtype) (htK : t ∈ K)
    (hfixed : omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W)
    (hgen : K ⊔ W = centralizer ({t} : Set S)) : False := by
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  have hWH : W < omegaCorePreimage S := by
    apply lt_of_le_of_ne (four_le_omegaCorePreimage hN S hZ W hW hno)
    intro heq
    have hc := card_omegaCorePreimage S
    rw [← heq, hW, hH] at hc
    contradiction
  have hproper : centralizer ({t} : Set S) ≠ ⊤ := by
    intro heq
    rw [heq, inf_top_eq] at hfixed
    exact (not_le_of_gt hWH) hfixed
  have ht2 : (⟨t, htK⟩ : K) ^ 2 = 1 := by
    apply Subtype.ext
    change t ^ 2 = 1
    simpa only [ht] using pow_orderOf_eq_one t
  have hline := centralizer_derived_eq_of_cyclic_four_section S.isPGroup'
    W (omegaCorePreimage S) hW hWH z hz hzc hzW K Z hquot hZK
    ⟨t, htK⟩ ht2 hfixed hgen
  exact S.not_isConj_of_saturated_centralizer_derived_line z t hz hzc
    hproper hline hsat hconj


/-- A saturated outside involution in the cyclic-four quaternion case cannot
be fused to the central involution. All action and fixed-core inputs are
proved from the quaternion factors. -/
public theorem quaternion_cyclic_four_false_of_saturated_centralizer
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4) [IsCyclic (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G))
    (hsat : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G), (t : G)} : Set G) →
      V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) : False := by
  let H := omegaCorePreimage S
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  obtain ⟨helem, hcard, horbit⟩ := quaternion_cyclic_four_fixed_core_and_orbit
    hN S hZ hindex B C hB hC hjoin hinter hcomm t ht hout
  have hsup := centralizer_sup_eq_top_of_involution_orbit H t ht2 horbit
  have hsurj := centralizer_quotient_surjective_of_involution_orbit H t ht2 horbit
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hclass : ⁅H,H⁆ ≤ center S := by
    rw [← map_subtype_commutator]
    apply (map_mono (IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient).trans
    exact central_of_normal_card_two ((center H).map H.subtype) (by
      rw [card_map_of_injective H.subtype_injective, IsExtraspecial.center_order_p 2 H])
  have hfixed : H ⊓ centralizer ({t} : Set S) = W :=
    hunique _ (fixed_core_normal_of_centralizer_supplement H t hsup hclass) helem hcard
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  have hcH : Nat.card H = 32 := (card_omegaCorePreimage S).trans hH
  have hline := centralizer_derived_eq_of_cyclic_four_fixed_four S.isPGroup'
    H W hindex (by omega) hW z t hz hzc hzW ht2 hfixed hsurj
  have hproper : centralizer ({t} : Set S) ≠ ⊤ := by
    intro he
    rw [he, inf_top_eq] at hfixed
    have hh := congrArg (fun K : Subgroup S => Nat.card K) hfixed
    omega
  exact S.not_isConj_of_saturated_centralizer_derived_line z t hz hzc
    hproper hline hsat hconj

/-- The cyclic-four exclusion with the full recognition interface. -/
public theorem quaternion_cyclic_four_false
    [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (_hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G))
    (hindex : (omegaCorePreimage S).index = 4)
    (hcyclic : IsCyclic (S ⧸ omegaCorePreimage S))
    (hsat : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G), (t : G)} : Set G) →
      V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype) : False := by
  let := hcyclic
  exact quaternion_cyclic_four_false_of_saturated_centralizer hN S hZ hno W hW hunique
    hH hindex B C hB hC hjoin hinter hcomm z hz hzc t ht hout hconj hsat

end Stellmacher.Recognition.NormalEightNonnormalImage
