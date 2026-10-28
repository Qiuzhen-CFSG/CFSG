module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.SimpleCoreImage
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The actual four-group offender from two elementary64 planes

The original elementary subgroup U has kernel U∩W of order16 on W64.
Its actual image is therefore elementary four, with fixed codimension two.
The simple parabolic quotient is retained in the same ambient action image.
-/

namespace Representation.BinaryInternalFixedSpaceCodimension
open Subgroup BinaryOffender
open scoped IsMulCommutative
variable {G S : Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]

public theorem core_four_offender
    (U W I L : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hI : I≤normalizer (W : Set G)) (hLI : L≤I) (hUL : U≤L)
    (hcore : L.pCoreIn 2=W) (hcomm : ⁅W,L⁆=W)
    (hUc : Nat.card U=64) (hWc : Nat.card W=64) (hinterc : Nat.card (U⊓W : Subgroup G)=16)
    (hfixed : W⊓centralizer (U : Set G)=U⊓W)
    (e : (L⧸pCore 2 L)≃*S) :
    let ρ := representation W I hI
    let τ := imageRepresentation ρ
    let A := actionSubgroup ρ (U.subgroupOf I)
    let C := actionSubgroup ρ (L.subgroupOf I)
    Nonempty (C≃*S) ∧ Nat.card A=4 ∧ IsOffender τ A ∧ A≤C := by
  let ρ := representation W I hI
  let τ := imageRepresentation ρ
  let A := actionSubgroup ρ (U.subgroupOf I)
  let C := actionSubgroup ρ (L.subgroupOf I)
  have hUI : U≤I := hUL.trans hLI
  have hW : W≠⊥ := by intro hh; rw [hh,card_bot] at hWc; omega
  obtain ⟨hk,he⟩ := simple_core_action_image W I L hI hLI hcore hcomm hW e
  have hsub : W.subgroupOf L=pCore 2 L := by
    change W.comap L.subtype=pCore 2 L
    rw [←hcore,pCoreIn,comap_map_eq_self_of_injective L.subtype_injective]
  have hker (u : I) (hu : (u:G)∈U) :
      u∈(actionHom ρ).ker ↔ (u:G)∈W := by
    let l : L := ⟨u,hUL hu⟩
    change l∈((actionHom ρ).comp (inclusion hLI)).ker ↔ (l:G)∈W
    rw [hk,←hsub]
    rfl
  have hinter : U.subgroupOf I⊓(actionHom ρ).ker=(U⊓W).subgroupOf I := by
    ext u
    constructor
    · rintro ⟨hu,hk⟩
      exact ⟨hu,(hker u hu).mp hk⟩
    · rintro ⟨hu,hw⟩
      exact ⟨hu,(hker u hu).mpr hw⟩
  have hAc : Nat.card A=4 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (U.subgroupOf I) (actionHom ρ)
    rw [hinter,Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hUI)).toEquiv,
      hinterc,Nat.card_congr (subgroupOfEquivOfLe hUI).toEquiv,hUc] at hh
    change 16*Nat.card A=64 at hh
    omega
  let : IsElementaryAbelian 2 (U.subgroupOf I) := IsElementaryAbelian.subgroupOf hUI
  have hAe : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAn : A≠⊥ := by intro hh; rw [hh,card_bot] at hAc; omega
  have hcodim : fixedCodim τ A=2 := by
    change fixedCodim (imageRepresentation ρ) (actionSubgroup ρ (U.subgroupOf I))=2
    rw [fixedCodim_actionSubgroup]
    have hh := fixedCodim_eq_finrank W I U hI hUI
    rw [hWc,hfixed,hinterc] at hh
    change _=fixedCodim ρ (U.subgroupOf I) at hh
    exact hh.symm.trans (by decide)
  refine ⟨he,hAc,⟨⟨hAn,hAe⟩,?_⟩,map_mono (subgroupOf_mono I hUL)⟩
  rw [hcodim,rank,hAc]
  decide

end Representation.BinaryInternalFixedSpaceCodimension
