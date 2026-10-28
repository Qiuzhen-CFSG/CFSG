module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SmallExclusions
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion
public import Theory.SpecificGroups.SymmetricEight.NormalFiveSeed

/-!
# The actual constrained A8 star row excludes a normal A5 seed

Embed the original whole star extension in S8, preserving its A8 marking.
The original radical image is a nontrivial two-subgroup normalized by the
literal seed image. The source Thompson normalizer bound puts its entire
even centralizer in the unchanged star local subgroup. Normality of the
seed there supplies the intrinsic eight-point obstruction.

Source: Aschbacher--Smith C.4.8 and 12.7.5, printed pp.153--154 and 840.
The actual seed, radical, projection, and A5 two-core quotient are retained;
no ambient Sylow, block-module equality, or splitting is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The unchanged constrained star component cannot be marked as A8. -/
theorem no_constrained_normal_a5_star_alternating_eight
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e8 : starImage (J.map H.subtype) R (J.map H.subtype) ≃*
      alternatingGroup (Fin 8)) : False := by
  let K := J.map H.subtype
  let C := starImage K R K
  let P := (L.subgroupOf K).map (toStarImage K R)
  let B := (starM K R M).subgroupOf C
  let s := h.constrained_source_input J hJ hq hout hf
  obtain ⟨hPB,hPn,hPc⟩ := h.constrained_normal_star_seed_component hn J hJ hq hout hf
  obtain ⟨a⟩ := h.constrained_normal_a5_star_seed_quotient hn eA5 J hJ hq hout hf
  obtain ⟨f,hfi,hfe⟩ := C27Source.alternating_star_embedding s (by decide) (by decide) e8
  let j : C →* Equiv.Perm (Fin 8) := f.comp C.subtype
  have hji : Function.Injective j := hfi.comp C.subtype_injective
  let Q := (starImage K R R).map f
  let P' := P.map j
  let d := P.equivMapOfInjective j hji
  let a' := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans a
  let : Group.IsPerfect (P.subgroupOf B) := hPc.perfect
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPB).toMonoidHom) (subgroupOfEquivOfLe hPB).surjective
  let : Group.IsPerfect P' := Group.IsPerfect.map j
  have hR : IsPGroup 2 R := by
    have hh := s.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le s.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q :=
    (hR.comap_subtype.map (QuotientGroup.mk' (starKernel K R))).map f
  have hQne : Q ≠ ⊥ := by
    intro hh
    let : (K.subgroupOf (K ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer s.normalizes)
    exact C27Source.star_radical_ne_bot (C27Source.source_join_input s)
      (((starImage K R R).map_eq_bot_iff_of_injective hfi).mp hh)
  have hPA : P' ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x,_,rfl⟩
    change f x ∈ _
    rw [hfe]
    exact (e8 x).property
  have hPQ : P' ≤ normalizer (Q : Set (Equiv.Perm (Fin 8))) := by
    rintro _ ⟨x,⟨k,hk,rfl⟩,rfl⟩
    apply (starImage K R R).le_normalizer_map f
    apply mem_map_of_mem
    apply (R.subgroupOf (K ⊔ R)).le_normalizer_map (QuotientGroup.mk' (starKernel K R))
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show R ≤ K ⊔ R from le_sup_right)]
    exact h.span_normalizes_radical (le_conjugateSpanBy L M hk)
  apply Theory.SpecificGroups.SymmetricEight.NormalFiveSeed.no_normal_five_seed
    Q P' hQ hQne hPA a' hPQ
  intro g hg
  let x : C := e8.symm ⟨g,hg.1⟩
  have hxg : j x = g := by
    change f x = g
    rw [hfe]
    exact congrArg Subtype.val (e8.apply_symm_apply ⟨g,hg.1⟩)
  have hxC : (x : StarQuotient K R) ∈ centralizer (starImage K R R : Set _) := by
    apply mem_centralizer_iff.mpr
    intro r hr
    apply hfi
    rw [map_mul,map_mul,show f x = g from hxg]
    exact mem_centralizer_iff.mp hg.2 (f r) (mem_map_of_mem f hr)
  have hJR : starImage K R (Stellmacher.elementaryAbelianMaxJ R) ≤ starImage K R R :=
    map_mono (comap_mono (sSup_le fun _ hA => hA.1))
  have hxJR : (x : StarQuotient K R) ∈ normalizer
      (starImage K R (Stellmacher.elementaryAbelianMaxJ R) : Set (StarQuotient K R)) := by
    apply Subgroup.centralizer_le_normalizer
    exact (centralizer_le (show
      (starImage K R (Stellmacher.elementaryAbelianMaxJ R) : Set (StarQuotient K R)) ⊆
        starImage K R R from hJR)) hxC
  have hxB : x ∈ B := by
    change (x : StarQuotient K R) ∈ starM K R M
    exact (C27Source.star_thompson_intersection_from_source s).1 ⟨x.property,hxJR⟩
  have hxN : x ∈ normalizer (P : Set C) :=
    (normal_subgroupOf_iff_le_normalizer hPB).mp hPn hxB
  exact P.le_normalizer_map j ⟨x,hxN,hxg⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
