module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.CoreStarNormalizerAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneGeometry
public import Theory.SpecificGroups.PSL2.BorelActorInner

/-!
# Marked Borel actors on the literal star component

Common normalizers preserve subgroup images under the star quotient and its
restricted component action. On a binary rank-one component, an actor subgroup
preserving the marked Thompson image and normalized by the marked Borel is
inner when its inner intersection is a 2-group. The proof transports the Sylow
normalizer through the specified group equivalence and applies the binary
PSL₂ Borel calculation.

Source: Aschbacher--Smith C.2.7 and the natural-row comparison in 14.6.15,
printed p.1035. The source application is in Quintic.SourceComponent.NaturalBorelAction.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] (K R : Subgroup G)

theorem starNormalizerAut_image (B : Subgroup G) (a : G)
    (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G))
    (hB : a ∈ normalizer (B : Set G)) :
    (starImage K R B).map (starNormalizerAut K R a hK hR).toMonoidHom =
      starImage K R B := by
  apply eq_of_le_of_card_ge
  · rintro x ⟨y,⟨b,hb,rfl⟩,rfl⟩
    change starNormalizerAut K R a hK hR (QuotientGroup.mk' (starKernel K R) b) ∈ _
    rw [starNormalizerAut_mk]
    refine mem_map_of_mem (QuotientGroup.mk' (starKernel K R)) ?_
    exact (mem_normalizer_iff.mp hB b).mp hb
  · exact (Nat.card_congr ((starNormalizerAut K R a hK hR).subgroupMap
      (starImage K R B)).toEquiv).le

theorem starComponentAction_image (B : Subgroup G)
    (hBC : starImage K R B ≤ starImage K R K)
    (a : (normalizer (K : Set G) ⊓ normalizer (R : Set G) : Subgroup G))
    (hB : (a : G) ∈ normalizer (B : Set G)) :
    ((starImage K R B).subgroupOf (starImage K R K)).map
      (starComponentAction K R a).toMonoidHom =
      (starImage K R B).subgroupOf (starImage K R K) := by
  apply map_injective (starImage K R K).subtype_injective
  rw [map_map,map_subgroupOf_eq_of_le hBC]
  have he : (starImage K R K).subtype.comp (starComponentAction K R a).toMonoidHom =
      (starNormalizerAut K R a a.property.1 a.property.2).toMonoidHom.comp
        (starImage K R K).subtype := by
        apply MonoidHom.ext
        intro x
        change ((starComponentAction K R a x : starImage K R K) : StarQuotient K R) =
          starNormalizerAut K R a a.property.1 a.property.2 x
        rw [starComponentAction_apply]
        exact starComponentAut_coe K R a a.property.1 a.property.2 x
  rw [he,←map_map,map_subgroupOf_eq_of_le hBC]
  exact starNormalizerAut_image K R B a a.property.1 a.property.2 hB

variable {K R} {H M : Subgroup G}
theorem rankOne_borel_actors_inner
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : starImage K R K ≃* SL(2,F.Carrier))
    (S : Sylow 2 (starImage K R K))
    (hS : (S : Subgroup _).map (starImage K R K).subtype =
      starImage K R (elementaryAbelianMaxJ R))
    (A : Subgroup (MulAut (starImage K R K)))
    (hA : A ≤ (starComponentAction K R).range)
    (hB : ((starM K R M).subgroupOf (starImage K R K)).map MulAut.conj ≤
      normalizer (A : Set _))
    (hi : IsPGroup 2 (A ⊓ MulAut.innerSubgroup (starImage K R K) : Subgroup _)) :
    A ≤ MulAut.innerSubgroup (starImage K R K) := by
  let C := starImage K R K
  have hSC : starImage K R (elementaryAbelianMaxJ R) ≤ C := by
    rw [←hS]
    exact map_subtype_le _
  have hSeq : (S : Subgroup C) =
      (starImage K R (elementaryAbelianMaxJ R)).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hSC]
  have hSP (α : MulAut C) (hα : α ∈ A) : (S : Subgroup C).map α.toMonoidHom = S := by
    obtain ⟨a,rfl⟩ := hA hα
    rw [hSeq]
    exact starComponentAction_image K R (elementaryAbelianMaxJ R) hSC a
      (normalizer_le_normalizer_elementaryAbelianMaxJ R a.property.2)
  have hn : normalizer (S : Set C) ≤ (starM K R M).subgroupOf C := by
    intro x hx
    apply (star_thompson_intersection_of_normal_input h).1
    refine ⟨x.property,?_⟩
    rw [←hS]
    exact (S : Subgroup C).le_normalizer_map C.subtype ⟨x,hx,rfl⟩
  exact Theory.PSL2.borelActorInner_of_mulEquiv F.Carrier
    (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL) S A hSP
    ((map_mono hn).trans hB) hi

end CFSG.Quasithin.ChapterC.C27Source
