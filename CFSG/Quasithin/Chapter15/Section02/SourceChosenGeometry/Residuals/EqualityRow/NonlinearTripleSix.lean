module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.TripleSix

/-!
# The original triple-six moved-section contradiction

The actual moved action and its offender generation put the Thompson image
inside the star component.  Its cubic center lies in the marked intersection;
the original component two-core lies there too, so this placement lifts to
the full central-core preimage.  Three-rank two forces a cubic intersection
with the residual, contradicting its two-group intersection with M.

The original quotient maps, selected component and full moved section are
retained.  The proof uses `ResidualInput` directly, without the missing
partner-residual identity.  The auxiliary cubic-center contradiction also
serves the other original component rows with the same marked center.
Source: Aschbacher--Smith C.2.7 and proof of 15.2.23, printed pp.145--147
and 1116--1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open ComponentCatalogue PlaneUniquenessPreceding ChapterC.C27Source
open PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The actual component two-core lifts cubic center placement to M ∩ I. -/
theorem ResidualInput.normalized_cubic_center_preimage_le_intersection
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hz : Nat.card (center (starImage X ((M ⊓ I).pCoreIn 2) X)) = 3)
    (hinner : starImage X ((M ⊓ I).pCoreIn 2) (elementaryAbelianMaxJ ((M ⊓ I).pCoreIn 2)) ≤
      starImage X ((M ⊓ I).pCoreIn 2) X) :
    centralCorePreimage X ≤ M ⊓ I := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  obtain ⟨P,hP⟩ := r.sylow_in_escape hI
  have hIP : I.pCoreIn 2 ≤ planeCentralizer T ⁅V,B⁆ :=
    (pCoreIn_le_sylow I P).trans_eq hP
  have hQ : X.pCoreIn 2 ≤ M ⊓ I := le_inf
    (((pCoreAmbient_mono_of_isSubnormalIn X I 2 selection.component.1
      selection.component.2.subnormal).trans hIP).trans
        (inf_le_left.trans hsource.maximal.1.2))
    ((pCoreIn_le 2 X).trans selection.component.1)
  have hk : pCore 2 X ≤ (M ⊓ I).subgroupOf X :=
    fun x hx => hQ (mem_map_of_mem X.subtype hx)
  rintro z ⟨x,hx,rfl⟩
  have hm := cubic_core_center_le_marked_intersection h hz hinner hx
  have hpre := comap_map_eq_self (f := QuotientGroup.mk' (pCore 2 X))
    (show (QuotientGroup.mk' (pCore 2 X)).ker ≤ (M ⊓ I).subgroupOf X by
      rwa [QuotientGroup.ker_mk'])
  exact (show x ∈ (M ⊓ I).subgroupOf X from hpre ▸ hm)

/-- A cubic star center with inner Thompson image contradicts the
original rank-two K and its two-group intersection with M. -/
theorem ResidualInput.normalized_component_false_of_cubic_star_center
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hz : Nat.card (center (starImage X ((M ⊓ I).pCoreIn 2) X)) = 3)
    (hinner : starImage X ((M ⊓ I).pCoreIn 2) (elementaryAbelianMaxJ ((M ⊓ I).pCoreIn 2)) ≤
      starImage X ((M ⊓ I).pCoreIn 2) X) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let a := cubicCenterCoreStarEquiv h hz
  let C := centralCorePreimage X
  let K := residual H
  have hCX : C ≤ X := map_subtype_le _
  have hCI : C ≤ I := hCX.trans selection.component.1
  have hKC : K ≤ normalizer (C : Set G) := selection.residual_normalizes.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hCM : C ≤ M :=
    (r.normalized_cubic_center_preimage_le_intersection hI hcore selection hz hinner).trans inf_le_left
  have hthree : 3 ∣ Nat.card C := by
    have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
    rw [map_centralPreimage,Nat.card_congr (centerCongr a).toEquiv,hz] at hh
    simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
  have hd := r.residual_intersection_three_dvd hI hCI hKC hthree
  have ht : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←r.residual_intersection_eq_core]
    exact inf_le_inf_left K hCM
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The actual triple-six moved action discharges both center and
Thompson-containment premises of the original-source contradiction. -/
theorem ResidualInput.normalized_component_tripleSix_false
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hgen : offenderSubgroup s.action =
      (starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))))
    (ha : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction s.action
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hr : quadraticRatio s.action = 1) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  apply r.normalized_component_false_of_cubic_star_center hI hcore selection
  · rw [←Nat.card_congr (centerCongr (subgroupOfEquivOfLe hCJ)).toEquiv,
      Nat.card_congr ha.centerEquiv.toEquiv]
    simp
  · exact ratio_one_thompson_inner_of_generated_component h hCJ s hgen hr

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
