module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Source

/-!
# The common source two-subgroup

The unchanged middle subgroup is T_F=AQ₅. Its image modulo A has order two,
so its order is4096. In the selected second parabolic of order12288 it is
an actual Sylow two-subgroup. The second core-intersection is exactly A.

Source: Aschbacher–Smith, J.4.5, printed p.442.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

def Plane.T_F (B5 : Sylow 5 d.toTypeRuSetup.H) : Subgroup G := p.A B5 ⊔ Q₅ d B5

theorem Plane.T_F_le_parabolic (B5 : Sylow 5 d.toTypeRuSetup.H) : p.T_F B5 ≤ p.parabolic :=
  sup_le (p.A_le_parabolic B5) (p.Q₅_le_parabolic B5)

theorem Plane.T_F_le_F₂ (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic) :
    p.T_F B5 ≤ p.F₂ B5 X := sup_le (p.A_le_F₂ B5 X) (p.Q₅_le_F₂ B5 X)

theorem SourceChoice.card_T_F (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (p.T_F B5)=4096 := by
  let C := (p.A B5).subgroupOf p.parabolic
  let M := (p.T_F B5).subgroupOf p.parabolic
  let q := QuotientGroup.mk' C
  have hCM : C ≤ M := comap_mono le_sup_left
  have hcardC : Nat.card C = 2048 :=
    (Nat.card_congr (subgroupOfEquivOfLe (p.A_le_parabolic B5)).toEquiv).trans (s.card_A p B5 hi)
  have himage : Nat.card (M.map q)=2 := by
    have he : M.map q = ((Q₅ d B5).subgroupOf p.parabolic).map q := by
      rw [show M = ((p.A B5) ⊔ Q₅ d B5).subgroupOf p.parabolic from rfl,
        subgroupOf_sup (p.A_le_parabolic B5) (p.Q₅_le_parabolic B5),Subgroup.map_sup]
      have hk : ((p.A B5).subgroupOf p.parabolic).map q=⊥ := QuotientGroup.map_mk'_self _
      rw [hk,bot_sup_eq]
    rw [he]
    exact s.Q₅_image_mod_A_card p B5 hi
  have hindex : (C.subgroupOf M).index=2 := by
    change C.relIndex M=2
    rw [← QuotientGroup.ker_mk' C,relIndex_ker]
    exact himage
  have hh := (C.subgroupOf M).index_mul_card
  rw [hindex,Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv,hcardC,
    Nat.card_congr (subgroupOfEquivOfLe (p.T_F_le_parabolic B5)).toEquiv] at hh
  exact hh.symm

/-- The supplied original middle subgroup is Sylow in the selected second endpoint. -/
theorem SourceChoice.T_F_sylow_F₂ (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    ∃ T : Sylow 2 (p.F₂ B5 X), (T : Subgroup (p.F₂ B5 X))=(p.T_F B5).subgroupOf (p.F₂ B5 X) := by
  let T := Sylow.ofCard (p := 2) ((p.T_F B5).subgroupOf (p.F₂ B5 X)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (p.T_F_le_F₂ B5 X)).toEquiv,
      s.card_T_F p B5 hi,s.card_F₂ p B5 hi X h,
      show 12288 = 2 ^ 12 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization])
  exact ⟨T,rfl⟩

/-- The intersection with the original radical is exactly the constructed core A. -/
theorem Plane.F₂_inf_R₂ (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    p.F₂ B5 X ⊓ p.R₂ = p.A B5 := by
  apply le_antisymm
  · have hh := inf_pCoreIn_le_of_le 2 (p.F₂_le_parabolic B5 X)
    rw [← p.R₂_eq,p.F₂_coreIn B5 X h] at hh
    exact hh
  · exact le_inf (p.A_le_F₂ B5 X) (p.A_le_R₂ B5)

end CFSG.Quasithin.ChapterJ.RuSubgroup
