module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Sylow
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ElementarySubgroups
/-!
# Elementary sixteen-groups in the ambient Sylow

The marked full root normalizer transports the graph–field obstruction:
an outside involution cannot centralize a noncentral root involution.
An elementary subgroup with an outside element meets R in at most the
four-element center, so its order is at most eight. Every elementary
subgroup inside R lies in one of its two root planes. Thus sixteen is the
maximum elementary order, and the two constructed planes exhaust that
maximum family, with no two-class census assumption.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(2), pp.257–258.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

theorem root_involution_centralized_by_outside (a r : G)
    (haN : a ∈ normalizer (P.R : Set G)) (ha : a ^ 2 = 1) (haR : a ∉ P.R)
    (hr : r ∈ P.R) (hr2 : r ^ 2 = 1) (hc : a * r = r * a) : r ∈ P.E := by
  obtain ⟨eR,eN,he⟩ := Geometry.Normalizer.exists_identification P
  let aN : normalizer (P.R : Set G) := ⟨a,haN⟩
  let rR : P.R := ⟨r,hr⟩
  have hmem : eR rR ∈ center RootNormalizerModel.Root := by
    by_contra hn
    have ha2 : (eN aN)^2=1 := by
      rw [←map_pow, eN.map_eq_one_iff]
      apply Subtype.ext
      simpa only [Subgroup.coe_pow,Subgroup.coe_one] using ha
    have hr2' : (eR rR)^2=1 := by
      rw [←map_pow, eR.map_eq_one_iff]
      apply Subtype.ext
      simpa only [Subgroup.coe_pow,Subgroup.coe_one] using hr2
    have hc' : eN aN * SemidirectProduct.inl (eR rR) =
        SemidirectProduct.inl (eR rR) * eN aN := by
      rw [←he rR,←map_mul,←map_mul]
      exact congrArg eN (Subtype.ext hc)
    obtain ⟨q,hq⟩ := RootNormalizerModel.involution_centralizes_root_involution
      (eN aN) (eR rR) ha2 hr2' hc' hn
    have heq : inclusion le_normalizer (eR.symm q) = aN := by
      apply eN.injective
      rw [he,eR.apply_symm_apply]
      exact hq
    have heq' : ((eR.symm q : P.R) : G) = a := congrArg Subtype.val heq
    exact haR (heq' ▸ (eR.symm q).property)
  have hcenter : rR ∈ center P.R := by
    rw [mem_center_iff]
    intro q
    apply eR.injective
    simpa only [map_mul] using (mem_center_iff.mp hmem (eR q))
  rw [←Geometry.E_center P]
  exact mem_map_of_mem P.R.subtype hcenter

/-- An elementary subgroup with an element outside R has order at most eight. -/
theorem elementary_outside_root_card_le_eight (S : Sylow 2 G)
    (hRS : P.R ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer (P.R : Set G)) (hS : Nat.card S = 128)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup G))
    (hn : ¬ A ≤ P.R) : Nat.card A ≤ 8 := by
  obtain ⟨a,ha,haR⟩ := SetLike.not_le_iff_exists.mp hn
  have hle : P.R ⊓ A ≤ P.E := by
    intro r hr
    apply P.root_involution_centralized_by_outside a r (hSN (hAS ha))
      (elemPow_eq_one_of_isElementaryAbelian a ha) haR hr.1
      (elemPow_eq_one_of_isElementaryAbelian r hr.2)
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a,ha⟩ : A) ⟨r,hr.2⟩)
  have hk : Nat.card (P.R.subgroupOf A) ≤ 4 := by
    rw [←inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe
      (show P.R ⊓ A ≤ A from inf_le_right)).toEquiv]
    exact (card_le_of_le hle).trans_eq P.E_card
  have hidx : P.R.relIndex (S : Subgroup G) = 2 := by
    have hh := (P.R.subgroupOf (S : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv,P.R_card,hS] at hh
    change 64 * P.R.relIndex (S : Subgroup G) = 128 at hh
    omega
  have hi : (P.R.subgroupOf A).index ≤ 2 := by
    have hh := P.R.relIndex_le_of_le_right hAS (by rw [hidx]; decide)
    rwa [hidx] at hh
  have hh := (P.R.subgroupOf A).card_mul_index
  have hb := Nat.mul_le_mul hk hi
  omega

/-- Every elementary subgroup inside R lies in one of its two root planes. -/
theorem elementary_in_root_le_plane (eR : P.R ≃* RootNormalizerModel.Root)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAR : A ≤ P.R) :
    A ≤ P.A₁ eR ∨ A ≤ P.A₂ eR := by
  let U := A.subgroupOf P.R
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hAR
  let V := U.map eR.toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  rcases Theory.GroupTheory.HyperbolicRecognition.elementary_le_rootPlane V with h | h
  · left
    intro a ha
    have hh := h (mem_map_of_mem eR.toMonoidHom
      (show (⟨a,hAR ha⟩ : P.R) ∈ U from ha))
    have hu : (⟨a,hAR ha⟩ : P.R) ∈ Theory.GroupTheory.HyperbolicRecognition.transportedPlane₁ eR := by
      apply (Theory.GroupTheory.HyperbolicRecognition.mem_transportedPlane₁ eR _).mpr
      exact (Theory.GroupTheory.HyperbolicRecognition.mem_rootPlane₁ _).mp hh
    exact mem_map_of_mem P.R.subtype hu
  · right
    intro a ha
    have hh := h (mem_map_of_mem eR.toMonoidHom
      (show (⟨a,hAR ha⟩ : P.R) ∈ U from ha))
    have hu : (⟨a,hAR ha⟩ : P.R) ∈ Theory.GroupTheory.HyperbolicRecognition.transportedPlane₂ eR := by
      apply (Theory.GroupTheory.HyperbolicRecognition.mem_transportedPlane₂ eR _).mpr
      exact (Theory.GroupTheory.HyperbolicRecognition.mem_rootPlane₂ _).mp hh
    exact mem_map_of_mem P.R.subtype hu

/-- Sixteen is the maximum elementary-subgroup order in the actual ambient Sylow. -/
theorem elementary_sylow_card_le_sixteen (S : Sylow 2 G)
    (hRS : P.R ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer (P.R : Set G)) (hS : Nat.card S = 128)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup G)) :
    Nat.card A ≤ 16 := by
  by_cases hAR : A ≤ P.R
  · obtain ⟨eR⟩ := Geometry.Coordinates.rootEquiv P
    rcases P.elementary_in_root_le_plane eR A hAR with h | h
    · exact (card_le_of_le h).trans_eq (P.A₁_card eR)
    · exact (card_le_of_le h).trans_eq (P.A₂_card eR)
  · exact (P.elementary_outside_root_card_le_eight S hRS hSN hS A hAS hAR).trans (by decide)

/-- Every elementary sixteen-group in the actual ambient Sylow lies in R. -/
theorem elementary_sixteen_le_root (S : Sylow 2 G)
    (hRS : P.R ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer (P.R : Set G)) (hS : Nat.card S = 128)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ (S : Subgroup G))
    (hA : Nat.card A = 16) : A ≤ P.R := by
  by_contra hn
  have hh := P.elementary_outside_root_card_le_eight S hRS hSN hS A hAS hn
  omega

theorem elementary_sixteen_in_sylow_iff (eR : P.R ≃* RootNormalizerModel.Root)
    (S : Sylow 2 G) (hRS : P.R ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer (P.R : Set G)) (hS : Nat.card S = 128)
    (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 16) ↔ A = P.A₁ eR ∨ A = P.A₂ eR := by
  constructor
  · rintro ⟨hE,hA⟩
    let := hE
    exact (P.elementary_sixteen_iff eR A
      (P.elementary_sixteen_le_root S hRS hSN hS A hAS hA)).mp ⟨hE,hA⟩
  · rintro (rfl | rfl)
    · exact ⟨inferInstance,P.A₁_card eR⟩
    · exact ⟨inferInstance,P.A₂_card eR⟩
end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
