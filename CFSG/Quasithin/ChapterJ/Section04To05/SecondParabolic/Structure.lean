module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Definitions
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The original second parabolic core and order

The actual preimage A is a two-group. Once the selected quotient F₂/A is S₃,
the two-core kernel theorem identifies O₂(F₂) with A, using the literal quotient
map. The earlier count of A then gives the source endpoint order12288.

Source: Aschbacher–Smith, J.4.5(4), printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The original A is a two-group before any endpoint recognition. -/
theorem Plane.A_isPGroup (B5 : Sylow 5 d.toTypeRuSetup.H) : IsPGroup 2 (p.A B5) :=
  d.T.isPGroup'.to_le ((p.A_le_R₂ B5).trans p.R₂_le_T)

theorem Plane.F₂_core (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    pCore 2 (p.F₂ B5 X) = (p.A B5).subgroupOf (p.F₂ B5 X) := by
  obtain ⟨e⟩ := h
  let q := QuotientGroup.mk' ((p.A B5).subgroupOf (p.F₂ B5 X))
  let f := e.toMonoidHom.comp q
  have hk : f.ker = (p.A B5).subgroupOf (p.F₂ B5 X) := by
    rw [MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := hk ▸ (p.A_isPGroup B5).comap_subtype
  exact (ker_eq_twoCore_of_surjective_perm_three f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hp).symm.trans hk

theorem Plane.F₂_coreIn (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    (p.F₂ B5 X).pCoreIn 2 = p.A B5 := by
  rw [pCoreIn,p.F₂_core B5 X h,map_subgroupOf_eq_of_le (p.A_le_F₂ B5 X)]

theorem SourceChoice.card_F₂ (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    Nat.card (p.F₂ B5 X) = 12288 := by
  obtain ⟨e⟩ := h
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]; decide
  rw [card_eq_card_quotient_mul_card_subgroup ((p.A B5).subgroupOf (p.F₂ B5 X)),
    Nat.card_congr e.toEquiv,h6,Nat.card_congr (subgroupOfEquivOfLe (p.A_le_F₂ B5 X)).toEquiv,
    s.card_A p B5 hi]

end CFSG.Quasithin.ChapterJ.RuSubgroup
