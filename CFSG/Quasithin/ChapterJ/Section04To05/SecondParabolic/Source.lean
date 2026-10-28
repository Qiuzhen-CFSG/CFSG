module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Structure
public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Kernel
public import Theory.GroupTheory.PCoreRestriction

/-!
# The actual second parabolic in J.4.4–5

The previously constructed normal four-group complement supplies the literal
order-two image of Q₅ in G₂/A. The source Sylow-selection theorem therefore
constructs X, retaining the chosen B₅ and original quotient. It proves Q₅
normalizes XA, F₂/A is S₃, O₂(F₂)=A, F₂S=G₂ and F₂∩S=S₂, and counts F₂.
Every input apart from the original choice of B₅ inverted by v is constructed.

Source: Aschbacher–Smith, J.4.4(5), J.4.5(4), printed pp.441–442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

theorem Plane.card_cubicSubgroup (X : Sylow 3 p.parabolic) : Nat.card (p.cubicSubgroup X)=3 := by
  rw [Plane.cubicSubgroup,card_map_of_injective p.parabolic.subtype_injective,p.card_sylow_three X]

/-- The source supplement identity uses the actual Sylow and full preimage A. -/
theorem SourceChoice.F₂_sup_S (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) (X : Sylow 3 p.parabolic) :
    p.F₂ B5 X ⊔ d.toTypeRuSetup.S = p.parabolic := by
  let M := p.F₂ B5 X ⊔ d.toTypeRuSetup.S
  have hMP : M ≤ p.parabolic := sup_le (p.F₂_le_parabolic B5 X) p.S_le_parabolic
  have hRM : p.R₂ ≤ M := by
    rw [← s.A_sup_S p B5 hi]
    exact sup_le ((p.A_le_F₂ B5 X).trans le_sup_left) le_sup_right
  have hTM : (d.T : Subgroup G) ≤ M := by
    rw [← p.R₂_sup_Q₅ B5]
    exact sup_le hRM ((p.Q₅_le_F₂ B5 X).trans le_sup_left)
  have ht : 16384 ∣ Nat.card M := by
    rw [← d.toTypeRuSetup.card_T_of_card_Z d.card_Z]
    exact card_dvd_of_le hTM
  have hx : 3 ∣ Nat.card M := by
    rw [← p.card_cubicSubgroup X]
    exact card_dvd_of_le (show p.cubicSubgroup X ≤ M from
      (le_sup_right.trans le_sup_left).trans le_sup_left)
  have hd : 49152 ∣ Nat.card M := by
    exact (by decide : Nat.Coprime 16384 3).mul_dvd_of_dvd_of_dvd ht hx
  apply eq_of_le_of_card_ge hMP
  rw [p.card_parabolic]
  exact Nat.le_of_dvd Nat.card_pos hd

/-- Intersecting F₂ with the original S recovers the literal S₂. -/
theorem SourceChoice.F₂_inf_S (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    p.F₂ B5 X ⊓ d.toTypeRuSetup.S = p.S₂ := by
  have hl : p.F₂ B5 X ≤ d.L := (p.F₂_le_parabolic B5 X).trans
    (fun x hx => ((p.mem_parabolic x).mp hx).1)
  have hc : p.F₂ B5 X ⊓ d.toTypeRuSetup.S ≤ p.A B5 := by
    rw [← p.F₂_coreIn B5 X h]
    exact inf_pCoreIn_le_of_le 2 hl
  apply le_antisymm
  · rw [← s.A_inf_S p B5 hi]
    exact le_inf hc inf_le_right
  · exact le_inf ((p.S₂_le_A B5).trans (p.A_le_F₂ B5 X)) p.S₂_le_S

/-- The original Q₅-normalized cubic lift, with its actual S₃ quotient. -/
theorem SourceChoice.exists_secondParabolic (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ X : Sylow 3 p.parabolic,
      Q₅ d B5 ≤ normalizer ((p.cubicSubgroup X ⊔ p.A B5 : Subgroup G) : Set G) ∧
      Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) ∧
      p.F₂ B5 X ⊔ d.toTypeRuSetup.S = p.parabolic ∧
      (p.F₂ B5 X).pCoreIn 2 = p.A B5 ∧
      p.F₂ B5 X ⊓ d.toTypeRuSetup.S = p.S₂ ∧ Nat.card (p.F₂ B5 X) = 12288 := by
  obtain ⟨X,hn,hm⟩ := p.exists_sylow_three_modulo B5 (p.A B5) (p.A_le_R₂ B5)
    (s.Q₅_image_mod_A_card p B5 hi)
  have hnorm : Q₅ d B5 ≤ normalizer ((p.cubicSubgroup X ⊔ p.A B5 : Subgroup G) : Set G) := by
    have h := (map_mono (f := p.parabolic.subtype) hn).trans
      (((X : Subgroup p.parabolic) ⊔ (p.A B5).subgroupOf p.parabolic).le_normalizer_map p.parabolic.subtype)
    rw [map_subgroupOf_eq_of_le (p.Q₅_le_parabolic B5),Subgroup.map_sup,
      map_subgroupOf_eq_of_le (p.A_le_parabolic B5)] at h
    exact h
  have hmodel := p.F₂_quotient_of_image B5 X hm
  exact ⟨X,hnorm,hmodel,s.F₂_sup_S p B5 hi X,p.F₂_coreIn B5 X hmodel,
    s.F₂_inf_S p B5 hi X hmodel,s.card_F₂ p B5 hi X hmodel⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
