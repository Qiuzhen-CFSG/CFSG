module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Middle
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers.Plane
public import Theory.GroupTheory.SylowPrimeIndexSelfNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The second endpoint satisfies the original rank-one local hypotheses

The original plane lies in A. Its pointwise centralizer in G₂ is R₂, so
F₂∩R₂=A makes O₂(F₂)=A self-centralizing. The generalized Fitting subgroup
therefore equals the two-core. The middle subgroup has prime index three
and is larger than the core, hence is self-normalizing.

These are the actual second-endpoint inputs of F.1.1 used in J.4.5,
Aschbacher–Smith, printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

theorem Plane.F₂_core_quotient (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((p.F₂ B5 X) ⧸ pCore 2 (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (p.F₂_core B5 X ⟨e⟩)).trans e⟩

theorem Plane.F₂_characteristic_two (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    Theory.GroupTheory.generalizedFitting (p.F₂ B5 X) = pCore 2 (p.F₂ B5 X) := by
  have hc := p.centralizer_le_of_plane_le (p.F₂_le_parabolic B5 X)
    (p.le_seed.trans (p.V_le_S₂.trans (p.S₂_le_A B5))) (p.F₂_inf_R₂ B5 X h)
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro x hx
  rw [p.F₂_core B5 X h]
  apply hc
  refine ⟨x.property,?_⟩
  intro a ha
  let aF : p.F₂ B5 X := ⟨a,p.A_le_F₂ B5 X ha⟩
  have haF : aF ∈ pCore 2 (p.F₂ B5 X) := by
    rw [p.F₂_core B5 X h]
    exact ha
  exact congrArg Subtype.val (hx aF haF)

theorem SourceChoice.T_F_normalizer_F₂ (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) (X : Sylow 3 p.parabolic)
    (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3))) :
    normalizer ((p.T_F B5).subgroupOf (p.F₂ B5 X) : Set (p.F₂ B5 X)) =
      (p.T_F B5).subgroupOf (p.F₂ B5 X) := by
  obtain ⟨S,hS⟩ := s.T_F_sylow_F₂ p B5 hi X h
  have hcard : Nat.card S=4096 := by
    rw [show Nat.card S = Nat.card (S : Subgroup (p.F₂ B5 X)) from rfl,hS,
      Nat.card_congr (subgroupOfEquivOfLe (p.T_F_le_F₂ B5 X)).toEquiv,s.card_T_F p B5 hi]
  have hi3 : S.index=3 := by
    have hh := S.card_mul_index
    rw [hcard,s.card_F₂ p B5 hi X h] at hh
    omega
  have hn : ¬ (S : Subgroup (p.F₂ B5 X)) ≤ pCore 2 (p.F₂ B5 X) := by
    intro he
    have hh := card_le_of_le he
    rw [hcard,p.F₂_core B5 X h,
      Nat.card_congr (subgroupOfEquivOfLe (p.A_le_F₂ B5 X)).toEquiv,s.card_A p B5 hi] at hh
    omega
  have he := S.normalizer_eq_of_prime_index_not_le_core (by rw [hi3]; decide) hn
  change normalizer ((S : Subgroup (p.F₂ B5 X)) : Set (p.F₂ B5 X)) = (S : Subgroup (p.F₂ B5 X)) at he
  rwa [hS] at he

/-- The unchanged source choices construct every second-endpoint local input. -/
theorem SourceChoice.exists_second_local (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀ a ∈ B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ X : Sylow 3 p.parabolic,
      p.F₂ B5 X ⊔ d.toTypeRuSetup.S = p.parabolic ∧
      (p.F₂ B5 X).pCoreIn 2 = p.A B5 ∧
      Nonempty (((p.F₂ B5 X) ⧸ pCore 2 (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)) ∧
      Theory.GroupTheory.generalizedFitting (p.F₂ B5 X) = pCore 2 (p.F₂ B5 X) ∧
      (∃ T : Sylow 2 (p.F₂ B5 X), (T : Subgroup (p.F₂ B5 X))=(p.T_F B5).subgroupOf (p.F₂ B5 X)) ∧
      normalizer ((p.T_F B5).subgroupOf (p.F₂ B5 X) : Set (p.F₂ B5 X)) =
        (p.T_F B5).subgroupOf (p.F₂ B5 X) := by
  obtain ⟨X,_,hmodel,hgen,hcore,_,_⟩ := s.exists_secondParabolic p B5 hi
  exact ⟨X,hgen,hcore,p.F₂_core_quotient B5 X hmodel,p.F₂_characteristic_two B5 X hmodel,
    s.T_F_sylow_F₂ p B5 hi X hmodel,s.T_F_normalizer_F₂ p B5 hi X hmodel⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
