module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSeven

/-!
# The original permutation row has seven letters

The original plane Sylow restricts to a full Sylow of the selected
component in M intersect I.  Its image normalizes the actual radical
image.  In the five-letter model this forces a full alternating Sylow
into that radical, making the original component a forbidden chi block.
This is the five-letter branch of the original symmetric-action exclusion;
all original star and action markings are retained.

Source: Aschbacher--Smith, C.2.7 and 15.2.23, printed pp.145--147 and
1116--1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open ComponentCatalogue PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The literal radical and Sylow marking exclude the original A₅ star row. -/
theorem ResidualInput.normalized_alternatingFive_false
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 5)) : False := by
  let R := (M ⊓ I).pCoreIn 2
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let J := X ⊔ R
  let C := starImage X R X
  let q := QuotientGroup.mk' (starKernel X R)
  let : (X.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer selection.radical_normalizes)
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hPS⟩ := r.component_sylow_in_plane hI selection.component
  have hP : (P : Subgroup X) ≤ (M ⊓ I).subgroupOf X := by
    intro x hx
    exact ⟨hsource.maximal.1.2 ((hPS hx).1),selection.component.1 x.property⟩
  let Pstar := P.mapSurjective (toStarImage_surjective X R)
  obtain ⟨f,hf,hmark⟩ := alternating_star_embedding h (by decide) (by decide) e
  have hNI : M ⊓ I ≤ normalizer (R : Set G) :=
    (M ⊓ I).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))
  have hn : (Pstar : Subgroup C).map C.subtype ≤
      normalizer (starImage X R R : Set (StarQuotient X R)) := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    apply (R.subgroupOf J).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show R ≤ J from le_sup_right)]
    exact hNI (hP hy)
  have hs := alternatingGroup.sylow_le_intersection_of_normalized_radical_five
    C (starImage X R R) e f hf hmark Pstar
    (star_radical_ne_bot (source_join_input h)) hn
    (star_intersection_normalizer_core_from_source h)
  exact star_radical_not_sylow h (selection.toSelected.not_chi hno) ⟨Pstar,hs⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
