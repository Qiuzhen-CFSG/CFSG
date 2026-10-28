module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Characteristic rigidity in a chosen local subgroup

This module formalizes the characteristic-subgroup transfer used in
Stellmacher (2.4), Journal of Algebra 190 (1997), p. 20.  A Sylow
2-subgroup `P` of the chosen local subgroup and the intrinsic Baumann
subgroup `BS` of the ambient Sylow subgroup have the same image `B` in the
ambient group.  Hence they are canonically isomorphic.

A characteristic subgroup of `P` transports to a characteristic subgroup
of `BS`, and characteristic transitivity makes its image characteristic in
the ambient Sylow subgroup.  If the original subgroup were normal in the
local group, then its common ambient image would be normalized by both the
local group and the ambient Sylow subgroup.  Their generation of the whole
group would make that image normal, contradicting the hypothesis of (2.4).
-/

namespace Stellmacher.SectionTwo

universe u v

private theorem characteristic_map_equiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (K : Subgroup A) (e : A ≃* B) (hK : K.Characteristic) :
    (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases hy with ⟨k, hk, rfl⟩
  let ψ : A ≃* A := e.trans (φ.trans e.symm)
  have hψK : K.map ψ.toMonoidHom ≤ K :=
    (Subgroup.characteristic_iff_map_le.mp hK) ψ
  refine ⟨ψ k, hψK ⟨k, hk, rfl⟩, ?_⟩
  change e (e.symm (φ (e k))) = φ (e k)
  exact e.apply_symm_apply _

/-- A characteristic subgroup of the chosen local Sylow subgroup cannot be
normal in the local group. -/
public theorem two_four_local_characteristic_not_normal
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (B L₁ : Subgroup G) (P : Sylow 2 L₁)
    (BS : Subgroup S) (hBSchar : BS.Characteristic)
    (hBSmap : BS.map (S : Subgroup G).subtype = B)
    (hPmap : P.map L₁.subtype = B)
    (hgen : L₁ ⊔ (S : Subgroup G) = ⊤)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal) :
    ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup L₁).subtype).Normal := by
  classical
  let eP₀ : P ≃* P.map L₁.subtype :=
    P.equivMapOfInjective L₁.subtype L₁.subtype_injective
  let eP : P ≃* B := eP₀.trans (MulEquiv.subgroupCongr hPmap)
  let eBS₀ : BS ≃* BS.map (S : Subgroup G).subtype :=
    BS.equivMapOfInjective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective
  let eBS : BS ≃* B := eBS₀.trans (MulEquiv.subgroupCongr hBSmap)
  let e : P ≃* BS := eP.trans eBS.symm
  have heP_ambient (x : P) :
      ((eP x : B) : G) = ((x : L₁) : G) := by
    simp only [eP, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply
      (P : Subgroup L₁) L₁.subtype L₁.subtype_injective x
  have heBS_ambient (x : BS) :
      ((eBS x : B) : G) = ((x : S) : G) := by
    simp only [eBS, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply
      BS (S : Subgroup G).subtype (S : Subgroup G).subtype_injective x
  have he_ambient (x : P) :
      ((e x : S) : G) = ((x : L₁) : G) := by
    rw [← heBS_ambient]
    simp only [e, MulEquiv.trans_apply, eBS.apply_symm_apply]
    exact heP_ambient x
  intro K hKchar hKne hKnormal
  let KB : Subgroup BS := K.map e.toMonoidHom
  have hKBchar : KB.Characteristic :=
    characteristic_map_equiv K e hKchar
  let KS : Subgroup S := KB.map BS.subtype
  let _ : BS.Characteristic := hBSchar
  let _ : KB.Characteristic := hKBchar
  have hKSchar : KS.Characteristic := by
    dsimp only [KS]
    infer_instance
  have hKSne : KS ≠ ⊥ := by
    intro hbot
    have hKBbot : KB = ⊥ := by
      apply Subgroup.map_injective BS.subtype_injective
      simpa only [Subgroup.map_bot] using hbot
    apply hKne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [KB, Subgroup.map_bot] using hKBbot
  let HG : Subgroup G := KS.map (S : Subgroup G).subtype
  have hHG_eq : HG =
      (K.map (P : Subgroup L₁).subtype).map L₁.subtype := by
    dsimp only [HG, KS, KB]
    simp only [Subgroup.map_map]
    apply congrArg (fun f => K.map f)
    ext x
    exact he_ambient x
  have hHGleS : HG ≤ (S : Subgroup G) := by
    dsimp only [HG]
    exact Subgroup.map_subtype_le _
  have hHGleL₁ : HG ≤ L₁ := by
    rw [hHG_eq]
    exact Subgroup.map_subtype_le _
  have hHGsubS : HG.subgroupOf (S : Subgroup G) = KS := by
    apply Subgroup.map_injective (S : Subgroup G).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hHGleS]
  have hHGsubL₁ : HG.subgroupOf L₁ =
      K.map (P : Subgroup L₁).subtype := by
    apply Subgroup.map_injective L₁.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hHGleL₁, hHG_eq]
  have hSnormHG : (S : Subgroup G) ≤ Subgroup.normalizer (HG : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hHGleS).mp
    rw [hHGsubS]
    exact Subgroup.normal_of_characteristic KS
  have hL₁normHG : L₁ ≤ Subgroup.normalizer (HG : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hHGleL₁).mp
    rw [hHGsubL₁]
    exact hKnormal
  have hHGnormal : HG.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hL₁normHG hSnormHG
  exact (hcharacteristic KS hKSchar hKSne) hHGnormal

end Stellmacher.SectionTwo
