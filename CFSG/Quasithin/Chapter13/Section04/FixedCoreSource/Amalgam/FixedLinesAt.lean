module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt

/-!
# The two original amalgam fixed lines at the same G,T

Maximal two-local uniqueness at the original component makes an escaping
vertex's fixed hyperplane disjoint from C_Z(L). Counting the two index-two
subgroups gives |Z|=4 and two distinct fixed lines of order two, with the
original fixed line C_Z(L)=C_V(L). Only Structural1222At at this G,T is used.
SeedGeometryAt and both component-module branches consume this geometry.
Source: Aschbacher--Smith 13.4.7(1), printed p.900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
/-- The source hyperplane argument for any escaping pair, with its literal two fixed lines. -/
theorem original_pair_fixed_lines_at {T : Sylow 2 G} {L V A B : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hdistinct : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G) ≠
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    Nat.card Z = 4 ∧ Nat.card F₁ = 2 ∧ Nat.card F₂ = 2 ∧
      F₁ ⊓ F₂ = ⊥ ∧ F₁ ⊔ F₂ = Z ∧
      Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (L : Set G)
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  have hbound (Y : Subgroup G) (hy : ¬ Y ≤ normalizer (L : Set G))
      (hi : (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2) : Nat.card Z ≤ 4 := by
    have hz : F ⊓ (Z ⊓ centralizer (Y : Set G)) = ⊥ := by
      apply eq_bot_iff.mpr
      intro d hd
      by_contra hd1
      apply hy
      apply le_trans ?_ (LocalGeometry.omega_fixed_generator_centralizer_le_normalizer_at
        h structural hd.1.1 hd.1.2 hd1)
      exact fun y hy => mem_centralizer_singleton_iff.mpr (hd.2.2 y hy)
    have hb := relIndex_inf_le (H := F) (K := Z ⊓ centralizer (Y : Set G)) (L := Z)
    rwa [hz,relIndex_bot_left,hindexL,hi] at hb
  have hc : Nat.card Z ≤ 4 := by
    by_cases hA : A ≤ normalizer (L : Set G)
    · exact hbound B (fun hB => hout (sup_le hA hB)) hindexB
    · exact hbound A hA hindexA
  have hfix : V ⊓ centralizer (L : Set G) ≤ F :=
    le_inf (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m) inf_le_right
  have hlow := card_le_of_le hfix
  rw [m.card_fixed] at hlow
  have hcount (Y : Subgroup G) :
      Nat.card (Z ⊓ centralizer (Y : Set G) : Subgroup G) *
        (Z ⊓ centralizer (Y : Set G)).relIndex Z = Nat.card Z := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
      (Z ⊓ centralizer (Y : Set G)) Z bot_le inf_le_left
    simpa only [relIndex_bot_left] using hh
  have hL := hcount L
  rw [hindexL] at hL
  change Nat.card F * 2 = Nat.card Z at hL
  have hZ : Nat.card Z = 4 := by change 2 ≤ Nat.card F at hlow; nlinarith
  have hFA := hcount A
  have hFB := hcount B
  rw [hindexA,hZ] at hFA
  rw [hindexB,hZ] at hFB
  change Nat.card F₁ * 2 = 4 at hFA
  change Nat.card F₂ * 2 = 4 at hFB
  have hF₁ : Nat.card F₁ = 2 := by omega
  have hF₂ : Nat.card F₂ = 2 := by omega
  have hinf : F₁ ⊓ F₂ = ⊥ := inf_eq_bot_of_card_two_of_ne F₁ F₂ hF₁ hF₂ hdistinct
  have hn : F₂ ≤ normalizer (F₁ : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hb.1).2.2 a
      ((mem_omegaOneCenterAmbient_iff _ _).mp ha.1).1
  have hs : F₁ ⊔ F₂ = Z := by
    apply eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint F₁ F₂ hn (disjoint_iff.mpr hinf),hF₁,hF₂,hZ]
  refine ⟨hZ,hF₁,hF₂,hinf,hs,?_⟩
  exact (eq_of_le_of_card_ge hfix (by rw [m.card_fixed]; rw [hZ] at hL; omega)).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
