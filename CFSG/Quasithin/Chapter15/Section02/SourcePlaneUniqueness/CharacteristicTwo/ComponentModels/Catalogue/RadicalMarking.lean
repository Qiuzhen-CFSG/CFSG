module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Preparation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow

/-!
# The original marked radical normalizer

When the actual Thompson image is inside the component, its normalizer
control and the normalization of R by NI identify the literal marked
subgroup with N(R* intersect X*). The intersection is two-radical. A Sylow
intersection would lift to R Sylow in XR, contradicting the source no-chi
conclusion. These facts support both the binary and linear-three flags.

Source: Aschbacher--Smith C.2.7, printed pp.145--147, and original 15.2.23,
printed pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

omit [Finite G] in
private theorem marking_normalizes (hM : M ≤ normalizer (R : Set G)) :
    (starM K R M).subgroupOf (starImage K R K) ≤
      normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K)) := by
  have hn : starM K R M ≤ normalizer (starImage K R R : Set (StarQuotient K R)) := by
    let D := K ⊔ R
    let q := QuotientGroup.mk' (starKernel K R)
    have hle : (M ⊓ K).subgroupOf D ≤ normalizer (R.subgroupOf D : Set D) := by
      rw [← subgroupOf_normalizer_eq (show R ≤ D from le_sup_right)]
      exact fun _ hx => hM hx.1
    exact (map_mono hle).trans ((R.subgroupOf D).le_normalizer_map q)
  intro x hx
  apply mem_normalizer_iff.mpr
  intro y
  exact mem_normalizer_iff.mp (hn hx) (y : StarQuotient K R)

/-- The original radical cannot contain a Sylow subgroup of the star component
without making the original component a forbidden chi-zero block. -/
theorem star_radical_not_sylow (h : Input KnownSimple.IsKnownSimple H R M K)
    (hc : ¬ ChapterC.IsChiBlock K) :
    ¬ ∃ S : Sylow 2 (starImage K R K),
      (S : Subgroup (starImage K R K)) ≤ (starImage K R R).subgroupOf (starImage K R K) := by
  rintro ⟨S, hS⟩
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  obtain ⟨P,hP⟩ := radical_sylow_of_star_component_sylow (source_join_input h) S
    (map_le_iff_le_comap.mpr hS)
  apply hc
  apply (source_chiZero_of_sylow_input h ?_).2.chi
  exact ⟨P,by rw [hP,map_subgroupOf_eq_of_le le_sup_right]⟩


/-- Actual inner Thompson containment identifies the source marking with the
normalizer of its nontrivial radical intersection. -/
theorem marked_radical_normalizer
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hM : M ≤ normalizer (R : Set G))
    (hi : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) ∧
      (starM K R M).subgroupOf (starImage K R K) =
        normalizer ((starImage K R R).subgroupOf (starImage K R K) :
          Set (starImage K R K)) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  refine ⟨star_intersection_radical_of_thompson_inner (source_join_input h) hi,?_⟩
  apply le_antisymm (marking_normalizes hM)
  simpa only [starM_inter_join] using
    star_intersection_normalizer_control_of_thompson_inner (source_join_input h) hi

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
