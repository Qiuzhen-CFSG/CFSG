module
public import Theory.SpecificGroups.AlternatingFiveSylowRadical
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RadicalMarking
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion

/-!
# Excluding the original five-letter star component

The original Sylow subgroup of I supplies a full Sylow of X inside NI.
Since NI normalizes R = O₂(NI), its image normalizes the literal radical
image in the star quotient. The alternating-five radical theorem puts
that full Sylow in R* intersect X*. The source Sylow lifting theorem then
makes X a chi-zero block, contradicting the original no-chi hypothesis.

This uses the actual selected component and quotient maps. It requires
neither an MS classification nor an assumed block reconstruction.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117, C.2.7,
pp.145--147, and the full-Sylow C.2.5 consequence of C.1.29.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem component_sylow_in_intersection
    (hI : PlaneEscapes Mc ZS I) (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ (M ⊓ I).subgroupOf X := by
  obtain ⟨S,hS⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let a := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyS : (y : I) ∈ S := by
    change y ∈ (S : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [←hQ]
  have hys : ((y : I) : G) ∈ planeSylow T ZS := hS ▸ mem_map_of_mem I.subtype hyS
  exact ⟨hsource.maximal.1.2 hys.1,(y : I).property⟩

include d in
/-- The original radical and Sylow marking exclude an A₅ star component. -/
theorem normalized_alternatingFive_false
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
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
  obtain ⟨P,hP⟩ := component_sylow_in_intersection d hI selection.component
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

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
