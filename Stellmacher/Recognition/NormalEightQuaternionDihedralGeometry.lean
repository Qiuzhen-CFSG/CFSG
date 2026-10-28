module

public import Stellmacher.Recognition.NormalEightQuaternionDihedralSetup
public import Stellmacher.Recognition.NormalEightQuaternionDihedralRotation
public import Stellmacher.Recognition.NormalEightQuaternionDihedralWitness

/-!
# Quaternion involution geometry over the dihedral quotient

The local action calculation splits into two independent parts: the fixed
four and single involution orbit over the nonidentity rotation square, and
the construction of a nonabelian fixed-eight involution. These imply the
precise geometry needed for the transfer argument.

The maximal subgroup is the preimage of the cyclic-four rotations. An
involution fixing a core of order eight is outside the core, since an inner
centralizer in the extraspecial core has order at least sixteen. If such an
involution lay above the rotations, the fixed-four calculation would rule
it out. The single involution orbit and elementary fixed core supply square
roots for the other involutions in the maximal subgroup.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
This module assembles the proved rotation and witness calculations into the
geometry conclusion under the original local hypotheses.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The fixed-four and single-core-orbit calculations give the required
outside-core square roots in the rotation preimage. -/
public theorem quaternionDihedralMaximal_involution_square
    (S : Sylow 2 G) (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (u : S) (huM : u ∈ quaternionDihedralMaximal S e)
    (huP : u ∉ omegaCorePreimage S) (hu : orderOf u = 2)
    (hfixed : IsElementaryAbelian 2
      (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S))
    (horbit : ∀ v : S, orderOf v = 2 →
      quaternionDihedralHom S e v = quaternionDihedralHom S e u →
      ∃ p : omegaCorePreimage S, (p : S) * u * (p : S)⁻¹ = v) :
    ∃ r : S, r ^ 2 = u := by
  let := hfixed
  apply DihedralGroup.square_root_of_rotation_involution (quaternionDihedralHom S e)
    (quaternionDihedralHom_surjective S e) u hu huM
    (fun h => huP ((quaternionDihedralHom_eq_one_iff S e u).mp h))
  · intro w hw hc
    exact elemPow_eq_one_of_isElementaryAbelian (A :=
      omegaCorePreimage S ⊓ centralizer ({u} : Set S)) w
      ⟨(quaternionDihedralHom_eq_one_iff S e w).mp hw,
        mem_centralizer_singleton_iff.mpr hc.eq⟩
  · intro v hv hf
    obtain ⟨p, hp⟩ := horbit v hv hf
    exact ⟨⟨p, by rw [quaternionDihedralHom_ker]; exact p.property⟩, hp⟩

/-- The two local quaternion calculations suffice for the complete geometry
premise of the dihedral transfer argument. -/
public theorem quaternion_dihedral_geometry_of_rotation_and_witness
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (hrotation : ∀ u : S, u ∈ quaternionDihedralMaximal S e →
      u ∉ omegaCorePreimage S → orderOf u = 2 →
      IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({u} : Set S) : Subgroup S) = 4 ∧
      ∀ v : S, orderOf v = 2 →
        quaternionDihedralHom S e v = quaternionDihedralHom S e u →
        ∃ p : omegaCorePreimage S, (p : S) * u * (p : S)⁻¹ = v)
    (hwitness : ∃ l : S, orderOf l = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8) :
    ∃ M : Subgroup S, M.index = 2 ∧
      (∀ x : S, orderOf x = 2 →
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 → x ∉ M) ∧
      (∀ u : S, u ∈ M → u ∉ omegaCorePreimage S → orderOf u = 2 → ∃ r : S, r ^ 2 = u) ∧
      ∃ l : S, orderOf l = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 := by
  refine ⟨quaternionDihedralMaximal S e, quaternionDihedralMaximal_index S e, ?_, ?_, hwitness⟩
  · intro x hx _ hcard hxM
    have hxP := not_mem_omegaCorePreimage_of_fixed_card_eight S hH x hcard
    have hfour := (hrotation x hxM hxP hx).2.1
    omega
  · intro u huM huP hu
    obtain ⟨he, _, ho⟩ := hrotation u huM huP hu
    exact quaternionDihedralMaximal_involution_square S e u huM huP hu he ho

/-- The quaternion factors and dihedral quotient supply the complete local
geometry needed by transfer. The maximal subgroup lies over the rotations. -/
public theorem quaternion_dihedral_geometry_of_quaternion_factors
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (he : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)) :
    ∃ M : Subgroup S, M.index = 2 ∧
      (∀ x : S, orderOf x = 2 →
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 → x ∉ M) ∧
      (∀ u : S, u ∈ M → u ∉ omegaCorePreimage S → orderOf u = 2 → ∃ r : S, r ^ 2 = u) ∧
      ∃ l : S, orderOf l = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 := by
  obtain ⟨e⟩ := he
  exact quaternion_dihedral_geometry_of_rotation_and_witness S hH e
    (quaternion_dihedral_rotation_of_quaternion_factors hN S hZ e B C hB hC hjoin hinter hcomm)
    (quaternion_dihedral_fixed_eight_witness hN S hZ hH B C hB hC hjoin hinter hcomm ⟨e⟩)

/-- The local geometry premise for the dihedral quotient exclusion, retaining
the full recognition hypotheses. In particular the excluded elementary eights
are only the normal ones. -/
public theorem quaternion_dihedral_geometry [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (_hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (_hW : Nat.card W = 4)
    (_hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (_hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (_hindex : 4 ≤ (omegaCorePreimage S).index)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (_hz : orderOf z = 2) (_hzc : z ∈ center S)
    (_ht : orderOf t = 2) (_htP : t ∉ omegaCorePreimage S)
    (_hzt : IsConj (z : G) (t : G))
    (he : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)) :
    ∃ M : Subgroup S, M.index = 2 ∧
      (∀ x : S, orderOf x = 2 →
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
        Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 → x ∉ M) ∧
      (∀ u : S, u ∈ M → u ∉ omegaCorePreimage S → orderOf u = 2 → ∃ r : S, r ^ 2 = u) ∧
      ∃ l : S, orderOf l = 2 ∧
        ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 := by
  exact quaternion_dihedral_geometry_of_quaternion_factors
    hN S hZ hH B C hB hC hjoin hinter hcomm he

end Stellmacher.Recognition.NormalEightNonnormalImage
