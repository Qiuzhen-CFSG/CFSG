module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSymplecticExclusion

/-!
# Alternating component placement and cubic-center exclusion

Cubic generation places the original wreath residual in each selected A₆
or A₇ component. In the equality row, solvability of the partner's cubic
closure makes that component escape the partner. The proper-Sylow rank
bound then rules out the ordinary A₆ core quotient. For any normal component
with cubic core center, C.2.6 places its full central preimage in M, whereas
three-rank two puts that center in the residual image. This contradicts
K intersect M = O₂(K). All maps retain the literal core, component and plane.

Source: Aschbacher--Smith 15.2.23, pp.1116--1117 and C.2.6--7,
refs/quasithin.pdf. No partner-residual identity is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
open TerminalLinear ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- Cubic generation places the actual residual inside the alternating component. -/
theorem ResidualInput.alternating_component_residual_le_M1
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (s : Selected H M I X)
    (hz : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) ≃*
      alternatingGroup (Fin n)) :
    residual H ≤ M1 X ⁅V,B⁆ := by
  refine le_inf ?_ r.residual_centralizes_plane
  rw [← alternating_component_cubic_closure (hsource := hsource) hI s hz hn e,
    ← r.residual_cubic_closure]
  apply Subgroup.closure_mono
  rintro x ⟨hx, ho⟩
  exact ⟨((le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right) hx, ho⟩

/-- Placement on the actual A₆ or A₇ star row, with its original radical and component. -/
theorem ResidualInput.alternating_star_residual_le_M1
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin n)) :
    residual H ≤ M1 X ⁅V,B⁆ := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  have hz : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3 := by
    rcases coreQuotient_center_card_from_source h with hh | hh <;> omega
  exact r.alternating_component_residual_le_M1 hI s.toSelected hz hn
    (alternatingStarCoreCenterEquiv h (by rcases hn with rfl | rfl <;> decide) e)

/-- The original partner intersection excludes an ordinary A₆ core quotient. -/
theorem ResidualInput.normalized_alternatingSix_no_ordinary_core_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6))
    (a : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 6)) : False := by
  let K := residual H
  have hK : K ≤ M1 X ⁅V,B⁆ := r.alternating_star_residual_le_M1 hI hcore s (Or.inl rfl) e
  have hKX : K ≤ X := hK.trans inf_le_left
  have hKM : K ≤ Mc :=
    (le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_left
  have hproper : Mc.subgroupOf X ≠ ⊤ := by
    intro ht
    exact r.alternating_component_not_le_partner_of_eq he hI hcore s (Or.inl rfl)
      (alternatingStarCoreCenterEquiv (normalized_component_input (hsource := hsource) hI hcore s)
        (by decide) e) (subgroupOf_eq_top.mp ht)
  obtain ⟨P,hPS⟩ := r.component_sylow_in_plane hI s.component
  have hP : (P : Subgroup X) ≤ Mc.subgroupOf X :=
    hPS.trans (subgroupOf_mono X ((le_sup_right.trans
      (r.residual_sup_planeCentralizer_le hI)).trans inf_le_left))
  have hu := Theory.SpecificGroups.SymmetricSix.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    a P (Mc.subgroupOf X) hP hproper
  have hl : 2 ≤ primeRank 3 (Mc.subgroupOf X) := by
    have hh := primeRank_mono 3 (show K.subgroupOf X ≤ Mc.subgroupOf X from fun _ hx => hKM hx)
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hKX), r.residual_rank_two] at hh
    exact hh
  omega

/-- An A₆ star image forces a cubic center in the full core quotient. -/
theorem ResidualInput.normalized_alternatingSix_core_center_three_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) :
    Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hc | hc
  · exact (r.normalized_alternatingSix_no_ordinary_core_of_eq he hI hcore s e
      (GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
        (alternatingStarCoreCenterEquiv h (by decide) e) hc)).elim
  · exact hc

/-- A normal component with cubic core center contradicts C.2.6 and residual rank. -/
theorem ResidualInput.normal_component_false_of_cubic_core_center
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : residual H ≤ X)
    (hz : Nat.card (center (X ⧸ pCore 2 X)) = 3) : False := by
  let C := centralCorePreimage X
  let K := residual H
  have hCM : C ≤ M :=
    (normal_component_central_preimage_le_intersection (hsource := hsource)
      hI hfit hcore hno hXI hn).trans inf_le_left
  let q := QuotientGroup.mk' (pCore 2 X)
  have hKrank : primeRank 3 ((K.subgroupOf X).map q) = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [show q.ker = pCore 2 X from QuotientGroup.ker_mk' _]; exact pCore_isPGroup),
      primeRank_congr 3 (subgroupOfEquivOfLe hKX),r.residual_rank_two]
  have hXrank : primeRank 3 (X ⧸ pCore 2 X) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact (primeRank_mono 3 hXI).trans
      ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hcenter := cubic_center_le_of_three_rank_two _ hKrank.ge hXrank hz
  have ht : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←r.residual_intersection_eq_core]
    exact inf_le_inf_left K hCM
  have hzle : center (X ⧸ pCore 2 X) ≤ ((K ⊓ C).subgroupOf X).map q := by
    intro z hz'
    obtain ⟨x,hx,he⟩ := hcenter hz'
    refine ⟨x,⟨hx,⟨x,?_,rfl⟩⟩,he⟩
    change q x ∈ center (X ⧸ pCore 2 X)
    rwa [he]
  have hzTwo : IsPGroup 2 (center (X ⧸ pCore 2 X)) :=
    ((ht.comap_subtype (K := X)).map q).to_le hzle
  obtain ⟨k,hk⟩ := hzTwo.exists_card_eq
  rw [hz] at hk
  have hd : 3 ∣ 2 ^ k := by rw [←hk]
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- Both possible central kernels in the actual A₆ row are impossible. -/
theorem ResidualInput.normalized_alternatingSix_false_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6)) : False := by
  have hz := r.normalized_alternatingSix_core_center_three_of_eq he hI hcore s e
  have hn := alternating_component_normalized (hsource := hsource) hI s.toSelected
    (by omega) (Or.inl rfl) (alternatingStarCoreCenterEquiv
      (normalized_component_input (hsource := hsource) hI hcore s) (by decide) e)
  exact r.normal_component_false_of_cubic_core_center hI hfit hcore hno s.component.1 hn
    ((r.alternating_star_residual_le_M1 hI hcore s (Or.inl rfl) e).trans inf_le_left) hz

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
