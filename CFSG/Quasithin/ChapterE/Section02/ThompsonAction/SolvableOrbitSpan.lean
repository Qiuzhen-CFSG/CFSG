module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NaturalOrbitSpan
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedOrbitSpan
public import Theory.Representation.NormalElementaryQuotient.MovedGeneration
/-!
# The complete solvable E.2.3 alpha orbit span

Use the same source natural factors and original quotient projections as
in the Baumann proof. Two sharp Thompson fixed spaces generate U. Its
actual odd-core fixed complement and residual moved-space identity then
replace U by [U,O²(H)] in the alpha orbit, retaining the literal fixed alpha
summand. Both possible factor counts are discharged internally.
Source: Aschbacher–Smith E.2.3(2), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem solvable_single_orbit_span_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker)) (hc : d.count = 1) :
    conjugateSpanBy (ChapterB.thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let D := d.toSolvableFFFactors
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp α hff hcore).1
  let j := D.singleAmbientHom hc
  have hji := D.singleAmbientHom_injective hfaith hcore hr hc
  have hjs := D.singleAmbientHom_surjective hc
  let q' := j.comp q
  have hq' : Function.Surjective q' := hjs.comp hq
  have hk' : q'.ker = centralizer (U : Set G) := by
    rw [← hker]
    ext g
    change j (q g) = 1 ↔ q g = 1
    exact (map_eq_one_iff j hji)
  let α' := NormalElementaryQuotient.representation U q' hq' hk'
  have heq (a : H) (v : Additive U) : α' (j a) v = α a v := by
    obtain ⟨g,rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U q' hq' hk' g v).trans
      (NormalElementaryQuotient.representation_apply U q hq hker g v).symm
  apply ChapterB.RankOneBaumann.natural_thompsonAlpha_orbit_span
    T hP U hU hJ q' hq' hk' (D.singleQuotientMap hfaith hr hc)
    (D.singleQuotientMap_surjective hfaith hr hc) ?_ ?_
  · intro a v
    obtain ⟨a,rfl⟩ := hjs a
    rw [heq, D.singleQuotientMap_equivariant]
    exact (D.singleAmbientHom_action hc a _).symm
  · rw [D.singleQuotientMap_ker]
    have hm : (pResidual 2 G).map q' = (pResidual 2 H).map j := by
      change (pResidual 2 G).map (j.comp q) = _
      rw [← Subgroup.map_map, map_pResidual_of_surjective 2 q hq]
    change fixedSpace α (pResidual 2 H) = fixedSpace α' ((pResidual 2 G).map q')
    rw [hm, ← fixedSpace_comp_map]
    have hrep : α = α'.comp j := MonoidHom.ext fun a =>
      LinearMap.ext fun v => (heq a v).symm
    rw [hrep]


private theorem solvable_pair_orbit_span_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker)) (hc : d.count = 2)
    (ht : ∀ i j, ∃ t : T,
      (d.factor i).map (MulAut.conj (q t)).toMonoidHom = d.factor j) :
    conjugateSpanBy (ChapterB.thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
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
  apply ChapterB.RankOneBaumann.paired_thompsonAlpha_orbit_span
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


theorem solvable_module_le_moved_sup_alpha_fixed
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker))
    (E : Subgroup G)
    (hfix : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ E) :
    U ≤ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔ (E ⊓ centralizer (pResidual 2 G : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let D := d.toSolvableFFFactors
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp α hff hcore).1
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hJY := ChapterB.RankOneBaumann.thompson_image_le_offender_layer T U q hq hker
    hUT (offenderSubgroup α) le_rfl
  have hRY : (pResidual 2 G).map q ≤ offenderSubgroup α := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hr
  have hs := (D.fixed_isCompl_moved hfaith hr).symm.sup_eq_top
  rw [← D.residual_moved_eq hfaith hr,← map_pResidual_of_surjective 2 q hq] at hs
  exact NormalElementaryQuotient.le_commutator_sup_fixed_of_generation U q hq hker
    (elementaryAbelianMaxJ (T : Subgroup G)) (pResidual 2 G) E (offenderSubgroup α) hJY hRY hs hfix


theorem source_solvable_orbit_span
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    conjugateSpanBy (ChapterB.thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let := hU.normal
  let := hU.elementary
  obtain ⟨d,hc,_,ht⟩ := source_solvable_factors T hP U hU hJ hrank hsolv
  have ha := (source_solvable_baumann_sylow_and_alpha T hP U hU hJ hrank hsolv).2
  have hfix : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      ChapterB.thompsonAlpha (T : Subgroup G) := le_sup_right.trans ha.ge
  have hbound := solvable_module_le_moved_sup_alpha_fixed T hP U hU (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ d _ hfix
  have hspan : conjugateSpanBy (ChapterB.thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
    rcases hc with hc | hc
    · exact solvable_single_orbit_span_of_factors T hP U hU (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ d hc
    · exact solvable_pair_orbit_span_of_factors T hP U hU (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ d hc ht
  rw [hspan]
  exact le_antisymm (sup_le hbound le_sup_right)
    (sup_le_sup_right (commutator_le_left _ _) _)
end CFSG.Quasithin.ChapterE.ThompsonAction
