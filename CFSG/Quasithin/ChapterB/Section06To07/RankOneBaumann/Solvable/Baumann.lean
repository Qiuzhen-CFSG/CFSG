module

public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Solvable.Pair
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.Single
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source

/-!
# The complete solvable Baumann branch of E.2.3

The genuine source witness has one or two natural binary factors. The first
case gives the whole centralizer quotient SL₂(2); the second uses the original
factor exchange. Both consume the constructed equivariant projection, with
its exact residual fixed kernel, in the proved Baumann source theorem.
No factor, module, Sylow or alpha conclusion is a hypothesis of the final
source theorem.

Source: Aschbacher–Smith E.2.3(2), printed pp.216–217 (1 March 2004).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.SolvableSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The original single binary factor gives the whole quotient SL₂(2), then Baumann's theorem. -/
theorem solvable_single_baumann_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker)) (hc : d.count = 1) :
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
  apply ChapterB.RankOneBaumann.natural_baumann_sylow_and_alpha
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

/-- The full solvable source branch of the Baumann Sylow and alpha conclusions. -/
theorem source_solvable_baumann_sylow_and_alpha
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (pResidual 2 G ⊔ ChapterB.baumann (T : Subgroup G)) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  let := hU.normal
  let := hU.elementary
  obtain ⟨d,hc,_,ht⟩ := source_solvable_factors T hP U hU hJ hrank hsolv
  rcases hc with hc | hc
  · exact solvable_single_baumann_of_factors T hP U hU (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ d hc
  · exact solvable_pair_baumann_of_factors T hP U hU (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ d hc ht

end CFSG.Quasithin.ChapterB.RankOneBaumann.SolvableSource
