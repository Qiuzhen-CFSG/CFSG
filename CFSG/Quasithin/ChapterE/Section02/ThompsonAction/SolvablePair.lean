module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedAssembly

/-!
# The genuine solvable paired Thompson and Baumann images

The source solvable factor theorem constructs the original S3 factors and
an element of the original Sylow exchanging them. The invariant odd-core
projection supplies a natural-pair quotient of the original elementary module,
so the paired image theorem applies with its original offender subgroup.
The conclusion retains the same centralizer quotient and actual Sylow images.

Source: Aschbacher–Smith E.2.3(1)–(2), printed pp.216–217 (1 March 2004).
This connects the two-factor source branch; the final Sylow and alpha argument
is supplied by the independent paired Baumann theorem.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The genuine two-factor solvable source witness gives the exact Thompson and Baumann images. -/
theorem solvable_pair_images_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 H = ⊥) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker))
    (hc : d.count = 2)
    (ht : ∀ i j, ∃ t : T,
      (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) :
    let α := NormalElementaryQuotient.representation U q hq hker
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ offenderSubgroup α ∧
      (ChapterB.baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ offenderSubgroup α := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let D := d.toSolvableFFFactors
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp α hff hcore).1
  let L := offenderSubgroup α
  let := offenderSubgroup_normal α
  apply ChapterB.RankOneBaumann.thompson_baumann_images_of_paired_quotient
    T U q hq hker hUT hJ L (D.pairActorCoordinates hc) (D.pairMovedAction hc)
    (D.pairMovedAction_injective hfaith hcore hr hc)
    (D.pairMovedAction_natural hc) (D.pairQuotientMap hfaith hr hc)
    (D.pairQuotientMap_surjective hfaith hr hc)
    (D.pairQuotientMap_equivariant hfaith hr hc) le_rfl
  obtain ⟨t,ht⟩ := ht ((finCongr hc).symm 0) ((finCongr hc).symm 1)
  refine ⟨t,t.property,?_,?_⟩
  · rw [D.pair_first_factor hc,D.pair_second_factor hc]
    exact ht
  · rw [D.pair_first_factor hc,D.pair_second_factor hc]
    exact D.pair_factor_exchange hc (q t) ht

/-- The original solvable E.2.3 witness, now carrying the paired Baumann-image conclusion. -/
theorem solvable_factors_and_pair_images
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 H = ⊥) (hsolv : Group.IsSolvable H) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) :
    let α := NormalElementaryQuotient.representation U q hq hker
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure α,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup α ∧
      (∀ i j, ∃ t : T,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) ∧
      (d.count = 2 →
        (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ offenderSubgroup α ∧
        (ChapterB.baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ offenderSubgroup α) := by
  obtain ⟨d,hc,hg,ht⟩ := solvable_factors T hP U q hq hker hcore hsolv hJ hrank
  exact ⟨d,hc,hg,ht,fun htwo =>
    solvable_pair_images_of_factors T hP U q hq hker hcore hUT hJ d htwo ht⟩


/-- The same constructed pair gives the original Baumann Sylow and alpha conclusions. -/
theorem solvable_pair_baumann_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker)) (hc : d.count = 2)
    (ht : ∀ i j, ∃ t : T,
      (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let D := d.toSolvableFFFactors
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp α hff hcore).1
  let L := offenderSubgroup α
  let := offenderSubgroup_normal α
  apply ChapterB.RankOneBaumann.paired_baumann_sylow_and_alpha
    T hP U hU hJ q hq hker L (D.pairActorCoordinates hc) (D.pairMovedAction hc)
    (D.pairMovedAction_injective hfaith hcore hr hc) (D.pairMovedAction_natural hc)
    (D.pairQuotientMap hfaith hr hc) (D.pairQuotientMap_surjective hfaith hr hc)
    (D.pairQuotientMap_equivariant hfaith hr hc) ?_ le_rfl ?_
  · rw [D.pairQuotientMap_ker, map_pResidual_of_surjective 2 q hq,
      D.fixed_residual_eq hfaith hr]
  · obtain ⟨t,ht⟩ := ht ((finCongr hc).symm 0) ((finCongr hc).symm 1)
    refine ⟨t,t.property,?_,?_⟩
    · rw [D.pair_first_factor hc,D.pair_second_factor hc]
      exact ht
    · rw [D.pair_first_factor hc,D.pair_second_factor hc]
      exact D.pair_factor_exchange hc (q t) ht

/-- The source reduced subgroup constructs the pair and all of its Baumann conclusions. -/
theorem source_solvable_factors_and_pair_baumann
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure α,
      (d.count = 1 ∨ d.count = 2) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup α ∧
      (∀ i j, ∃ t : T,
        (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) ∧
      (d.count = 2 →
        Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
          (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
        ChapterB.thompsonAlpha (T : Subgroup G) =
          (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))) := by
  let := hU.normal
  let := hU.elementary
  obtain ⟨d,hc,hg,ht⟩ := source_solvable_factors T hP U hU hJ hrank hsolv
  exact ⟨d,hc,hg,ht,fun htwo => solvable_pair_baumann_of_factors T hP U hU
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hU.quotient_pCore_eq_bot hJ d htwo ht⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
