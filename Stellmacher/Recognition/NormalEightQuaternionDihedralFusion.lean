module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightQuaternionAbelianSetup
public import Stellmacher.Recognition.NormalEightQuaternionDihedralLine
public import Stellmacher.Recognition.NormalEightQuaternionDihedralCoreSeparation
public import Theory.GroupTheory.NormalSubgroupFixedConjugacy
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.GroupTheory.SaturatedInvolutionSquareFusion

/-!
# Local selection for the quaternion-core dihedral quotient

Conjugacy in the central-omega normalizer preserves the full isomorphism type
of the fixed core: the core preimage maps isomorphically onto the normal
two-core of the odd-core quotient. Thus an involution with nonabelian fixed
core of order eight can be chosen with saturated local centralizer without
losing either fixed-core property.

A derived-center line identifying the central involution upgrades this local
saturation to saturation in the ambient centralizer. The quaternion line
calculation and core-fusion exclusion discharge the conditional assembly,
giving the fusion premise for transfer. No bound on arbitrary elementary
eights is assumed.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Local conjugacy preserves the entire fixed-core group, not just core membership. -/
public theorem omegaCorePreimage_fixed_equiv_of_local_isConj
    (S : Sylow 2 G) (x y : S)
    (hxy : IsConj (inclusion (sylow_le_omegaNormalizer S) x)
      (inclusion (sylow_le_omegaNormalizer S) y)) :
    Nonempty ((omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ≃*
      (omegaCorePreimage S ⊓ centralizer ({y} : Set S) : Subgroup S)) := by
  apply nonempty_fixed_equiv_of_isConj_map (omegaQuotientHom S)
    (omegaQuotientHom_injective S) (pCore 2 (OmegaQuotient S))
  · rw [omegaQuotientHom_range]
    exact pCore_isPGroup.le_sylow_of_normal _
  · rw [omegaQuotientHom_apply, omegaQuotientHom_apply]
    exact (QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))).map_isConj hxy

/-- Select a locally saturated representative while preserving the nonabelian
fixed-eight type and the involution order. -/
public theorem exists_fixed_eight_with_saturated_local_centralizer
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (l : S) (hl : orderOf l = 2)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8) :
    ∃ x : S, orderOf x = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 ∧
      x ∉ omegaCorePreimage S ∧
      IsConj (inclusion (sylow_le_omegaNormalizer S) l)
        (inclusion (sylow_le_omegaNormalizer S) x) ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ omegaNormalizer S → V ≤ centralizer ({(x : G)} : Set G) →
        V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype := by
  obtain ⟨x, hlx, hout, hmax⟩ :=
    exists_outside_conjugate_with_saturated_local_centralizer S l
      (not_mem_omegaCorePreimage_of_fixed_card_eight S hH l hcard)
  obtain ⟨e⟩ := omegaCorePreimage_fixed_equiv_of_local_isConj S l x hlx
  have hx : orderOf x = 2 := by
    have hc := (omegaNormalizer S).subtype.map_isConj hlx
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    change g * (l : G) * g⁻¹ = (x : G) at hg
    rw [← orderOf_coe x, ← hg, ← MulAut.conj_apply]
    exact ((MulAut.conj g).orderOf_eq (l : G)).trans ((orderOf_coe l).trans hl)
  refine ⟨x, hx, ?_, (Nat.card_congr e.toEquiv).symm.trans hcard, hout, hlx, hmax⟩
  intro hc
  let := hc
  apply hnonab
  exact ⟨⟨fun a b => e.injective (by
    simpa only [map_mul] using mul_comm' (e a) (e b))⟩⟩

/-- The characteristic derived-center line upgrades local saturation to
ambient saturation by the two-group normalizer condition. -/
public theorem saturated_centralizer_of_local_and_derived_center_line
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z x : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hline : let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G))
    (hlocal : ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ omegaNormalizer S → V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) :
    ∀ V : Subgroup G, IsPGroup 2 V →
      (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(x : G)} : Set G) →
      V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype := by
  apply saturated_of_normalizer_control _ (omegaNormalizer S)
  · intro V hVp hEV hVC
    exact hlocal V hVp hEV (hVC.trans inf_le_left) (hVC.trans inf_le_right)
  · rw [omegaNormalizer_eq_centralizer_of_central_involution S hZ z hz hzc]
    exact inf_le_left.trans (normalizer_le_centralizer_of_derived_center_line _
      (z : G) ((orderOf_coe z).trans hz) hline)

/-- Local selection and the two quaternion centralizer calculations give
exactly the fusion input for the dihedral transfer argument. -/
public theorem quaternion_dihedral_fusion_of_line_and_core_separation
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hline : ∀ x : S, orderOf x = 2 →
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
      Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 →
      let E := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (_root_.commutator E ⊓ center E).map E.subtype = zpowers (z : G))
    (hseparate : ∀ x : S, orderOf x = 2 →
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) →
      Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 →
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(x : G)} : Set G) →
        V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) →
      ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G))
    (l : S) (hl : orderOf l = 2)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8) :
    ∃ x : S, orderOf x = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 ∧
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(x : G)} : Set G) →
        V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) ∧
      ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G) := by
  obtain ⟨x, hx, hxnonab, hxcard, _, _, hlocal⟩ :=
    exists_fixed_eight_with_saturated_local_centralizer S hH l hl hnonab hcard
  have hmax := saturated_centralizer_of_local_and_derived_center_line
    S hZ z x hz hzc (hline x hx hxnonab hxcard) hlocal
  exact ⟨x, hx, hxnonab, hxcard, hmax, hseparate x hx hxnonab hxcard hmax⟩

/-- Every involution with nonabelian fixed core of order eight has a representative
of the same fixed-core type whose centralizer is saturated in the ambient group
and which is not conjugate to any element of the core. This is the fusion premise
for the quaternion-core dihedral transfer argument. -/
public theorem quaternion_dihedral_fusion
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
    (l : S) (hl : orderOf l = 2)
    (hnonab : ¬ IsMulCommutative
      (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S))
    (hcard : Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8) :
    ∃ x : S, orderOf x = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({x} : Set S) : Subgroup S) = 8 ∧
      (∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(x : G)} : Set G) →
        V = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype) ∧
      ∀ u : S, u ∈ omegaCorePreimage S → ¬ IsConj (x : G) (u : G) := by
  have hline := quaternion_dihedral_ambient_line hN S hZ hno W hW hH hquot
    B C hB hC hjoin hinter hcomm z hz hzc
  apply quaternion_dihedral_fusion_of_line_and_core_separation
    S hZ hH z hz hzc hline ?_ l hl hnonab hcard
  intro x hx hxnonab hxcard hmax
  exact quaternion_dihedral_core_separation hN S hZ hH z hz hzc x hx hxcard
    (hline x hx hxnonab hxcard) hmax

end Stellmacher.Recognition.NormalEightNonnormalImage
