module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Action
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection

/-!
# Central intersections in the original natural-action alternatives

For a local module of order four, its fixed subgroup under J(T) is a
proper subgroup containing the original central involutions. The general
elementary fixed-center identity forces E ∩ V = Z of order two. In the
orthogonal case the existing actual Sylow geometry gives |E ∩ V| = 4
and |Z| = 2. Both are assembled with the previously proved compatible
quotient-action coordinates from the original source hypotheses.

The final theorem is the literal V(M) consumer of Aschbacher–Smith
14.1.7, printed p.977. The arbitrary reduced-module action alternatives
remain available in NaturalModels.Action.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

theorem local_alpha_of_order_four (T : Sylow 2 G) (M : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)]
    (hVT : localModule T M ≤ (T : Subgroup G))
    (hcard : Nat.card (localModule T M) = 4)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M = centralInvolutions T ∧
      Nat.card (centralInvolutions T) = 2 := by
  let V := localModule T M
  let F := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  have hEq : ChapterB.thompsonAlpha (T : Subgroup G) ⊓ V = F :=
    omegaCenter_maxJ_inf_elementary_eq_fixed _ _ hVT
  have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
  have hZF : centralInvolutions T ≤ F := by
    rw [← hEq]
    exact le_inf (omegaCenter_le_omegaCenter_maxJ _) hZV
  have hZn : centralInvolutions T ≠ ⊥ := by
    intro hZ
    have hV : V = ⊥ := bot_unique (conjugateSpanBy_le hZ.le le_normalizer_of_normal)
    have hc : Nat.card V = 4 := hcard
    rw [hV, card_bot] at hc
    contradiction
  have hFn : F ≠ ⊥ := fun h => hZn (bot_unique (hZF.trans_eq h))
  have hFV : F ≠ V := by
    intro he
    apply hJ
    apply le_centralizer_iff.mpr
    exact he.symm.le.trans inf_le_right
  have hd : Nat.card F ∣ 2 ^ 2 := by
    have h := card_dvd_of_le (show F ≤ V from inf_le_left)
    rw [show Nat.card V = 4 from hcard] at h
    exact h
  have hFc : Nat.card F = 2 := by
    obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · exact (hFn (F.eq_bot_of_card_eq hc)).elim
    · exact hc
    · have he : F = V := eq_of_le_of_card_ge inf_le_left (by rw [hcard, hc]; decide)
      exact (hFV he).elim
  have hZc : Nat.card (centralInvolutions T) = 2 := by
    have hlo := ((centralInvolutions T).one_lt_card_iff_ne_bot.mpr hZn)
    have hhi := Nat.card_le_card_of_injective _ (inclusion_injective hZF)
    rw [hFc] at hhi
    omega
  have hZF' : centralInvolutions T = F := eq_of_le_of_card_ge hZF (by rw [hZc, hFc])
  exact ⟨hEq.trans hZF'.symm, hZc⟩

theorem local_alpha_of_orthogonal (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    Nat.card (localModule T M) = 16 ∧
      Nat.card ↥(ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M) = 4 ∧
      Nat.card (centralInvolutions T) = 2 ∧
      centralInvolutions T ≤ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M) := by
  have h := orthogonal_noncentral_of_geometry T d hTM 1 hJ
    (d.elementary_image_planeStabilizer T hTM 1)
    (d.card_image_planeStabilizer T hTM 1)
    (d.card_fixedPlane_planeStabilizer T hTM 1)
  refine ⟨d.card_vector, ?_, d.card_centralInvolutions T hTM, ?_⟩
  · rw [h.2.2.2.1]
    exact d.card_fixedPlane_planeStabilizer T hTM 1
  · exact le_inf (omegaCenter_le_omegaCenter_maxJ _) (le_conjugateSpanBy _ _)


universe u

theorem local_14_1_7_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let hH : M ∈ Chapter1.HOver G (T : Set G) :=
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
    let U := (localModule T M).subgroupOf M
    letI := (localModule_reduced_from_source hG T hH).normal
    letI := (localModule_reduced_from_source hG T hH).elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      (∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∧
      Nat.card (localModule T M) = 4 ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M = centralInvolutions T ∧
      Nat.card (centralInvolutions T) = 2) ∨
    (Nonempty (NaturalOrthogonalAction M (localModule T M)) ∧
      Nat.card (localModule T M) = 16 ∧
      Nat.card ↥(ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M) = 4 ∧
      Nat.card (centralInvolutions T) = 2 ∧
      centralInvolutions T ≤ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M)) := by
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let U := (localModule T M).subgroupOf M
  have hU := localModule_reduced_from_source hG T hH
  let := hU.normal
  let := hU.elementary
  let := localModule_elementary_from_source hG T hH
  have hVM : localModule T M ≤ M := localModule_le T hM.2
  have hVT : localModule T M ≤ (T : Subgroup G) := by
    have h := (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal (T.subtype hM.2)
    intro v hv
    exact h (show (⟨v, hVM hv⟩ : M) ∈ U from hv)
  rcases local_natural_action_from_source hA hC hG T hempty hM hunique hcase hJ with h | h
  · obtain ⟨c, e, hc⟩ := h
    have hcard : Nat.card (localModule T M) = 4 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv]
      change Nat.card (Additive U) = 4
      rw [Nat.card_congr c.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    exact Or.inl ⟨c, e, hc, hcard, local_alpha_of_order_four T M hVT hcard hJ⟩
  · obtain ⟨d⟩ := h
    exact Or.inr ⟨⟨d⟩, local_alpha_of_orthogonal T hM.2 d hJ⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
