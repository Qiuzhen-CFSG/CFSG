module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightNonnormalCyclicWeakClosure
public import Stellmacher.Recognition.NormalEightQuaternionDihedralRotation
public import Theory.GroupTheory.DihedralCentralizerQuotient
public import Theory.GroupTheory.PGroup.ExtraspecialFixedCentralizerLocalLine

/-!
# The characteristic line of a dihedral-quotient fixed-eight centralizer

For an involution with nonabelian fixed core of order eight, a noncentral
image in the dihedral quotient makes the centralizer quotient abelian.
The normal extraspecial fixed core then identifies the derived-center line
with the central involution, intrinsically and after embedding in the
ambient group. Being outside an index-two subgroup containing the core
is a sufficient geometric input.

The quaternion rotation calculation excludes a fixed-eight involution from
the rotation preimage: an involution there has fixed core of order four.
This discharges the geometric input and gives the unconditional line.
No saturation or bound on arbitrary elementary abelian subgroups is used.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic fixed-eight line when the involution has noncentral dihedral image. -/
public theorem quaternion_dihedral_intrinsic_line_of_noncentral_image
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8)
    (hx : QuotientGroup.mk' (omegaCorePreimage S) x ∉ center (S ⧸ omegaCorePreimage S)) :
    (_root_.commutator (centralizer ({x} : Set S)) ⊓
      center (centralizer ({x} : Set S))).map
      (centralizer ({x} : Set S)).subtype = zpowers z := by
  let := centralizer_quotient_commutative_of_dihedral_noncentral (omegaCorePreimage S) e x hx
  exact centralizer_derived_inf_center_line_of_nonabelian_eight (omegaCorePreimage S)
    z x hz hzc (central_involution_mem_omegaCorePreimage hN S hZ W hW hno z hzc hz)
    hcard hnonab

/-- The characteristic fixed-eight line in the original ambient group. -/
public theorem quaternion_dihedral_ambient_line_of_noncentral_image
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8)
    (hx : QuotientGroup.mk' (omegaCorePreimage S) x ∉ center (S ⧸ omegaCorePreimage S)) :
    let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
    (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G) := by
  exact map_derived_inf_center_line (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective (centralizer ({x} : Set S)) z
    (quaternion_dihedral_intrinsic_line_of_noncentral_image hN S hZ hno W hW e
      z x hz hzc hnonab hcard hx)

/-- The line calculation consumes exclusion from an index-two subgroup above the core. -/
public theorem quaternion_dihedral_ambient_line_of_not_mem_maximal
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (M : Subgroup S) (hM : M.index = 2) (hPM : omegaCorePreimage S ≤ M)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8)
    (hx : x ∉ M) :
    let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
    (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G) := by
  exact quaternion_dihedral_ambient_line_of_noncentral_image hN S hZ hno W hW e
    z x hz hzc hnonab hcard
    (quotient_noncentral_of_not_mem_index_two (omegaCorePreimage S) M e hM hPM x hx)

/-- A fixed-eight involution has noncentral dihedral image: it lies outside
both the core and the rotation preimage. -/
public theorem quaternion_dihedral_noncentral_image_of_fixed_eight
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (e : (S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : S) (hx : orderOf x = 2)
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8) :
    QuotientGroup.mk' (omegaCorePreimage S) x ∉ center (S ⧸ omegaCorePreimage S) := by
  have hxP := not_mem_omegaCorePreimage_of_fixed_card_eight S hH x hcard
  have hxM : x ∉ quaternionDihedralMaximal S e := by
    intro hxM
    have hfour := (quaternion_dihedral_rotation_of_quaternion_factors
      hN S hZ e B C hB hC hjoin hinter hcomm x hxM hxP hx).2.1
    omega
  exact quotient_noncentral_of_not_mem_index_two (omegaCorePreimage S)
    (quaternionDihedralMaximal S e) e (quaternionDihedralMaximal_index S e)
    (omegaCorePreimage_le_quaternionDihedralMaximal S e) x hxM

/-- The intrinsic characteristic line for a nonabelian fixed core of order eight
in the quaternion-core dihedral branch, without a saturation assumption. -/
public theorem quaternion_dihedral_intrinsic_line
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hquot : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4))
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (x : S) (hx : orderOf x = 2)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8) :
    (_root_.commutator (centralizer ({x} : Set S)) ⊓
      center (centralizer ({x} : Set S))).map
      (centralizer ({x} : Set S)).subtype = zpowers z := by
  obtain ⟨e⟩ := hquot
  exact quaternion_dihedral_intrinsic_line_of_noncentral_image hN S hZ hno W hW e
    z x hz hzc hnonab hcard
    (quaternion_dihedral_noncentral_image_of_fixed_eight hN S hZ hH e
      B C hB hC hjoin hinter hcomm x hx hcard)

/-- The derived-center line in the ambient group for every involution with
nonabelian fixed core of order eight in the quaternion-core dihedral branch. -/
public theorem quaternion_dihedral_ambient_line
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hquot : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4))
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (x : S) (hx : orderOf x = 2)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8) :
    let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
    (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G) := by
  exact map_derived_inf_center_line (S : Subgroup G).subtype
    (S : Subgroup G).subtype_injective (centralizer ({x} : Set S)) z
    (quaternion_dihedral_intrinsic_line hN S hZ hno W hW hH hquot
      B C hB hC hjoin hinter hcomm z hz hzc x hx hnonab hcard)

end Stellmacher.Recognition.NormalEightNonnormalImage
