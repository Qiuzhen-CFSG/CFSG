module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairMovedGeneration
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedOrbitSpan
public import Theory.Representation.NormalElementaryQuotient.MovedGeneration
/-!
# The literal paired E.2.3 alpha orbit span

The genuine source pair consists of actual moved summands. Its central
quotient decomposition and residual generation imply that U is generated
by [U,O²(H)] and C_U(Y), for the original offender group Y. The latter
subgroup centralizes both J(T) and O²(H). Combining this with the sharp
two-conjugate orbit calculation proves the precise source identity.
Source: Aschbacher–Smith B.6.9–10 and E.2.3(2), pp.115–117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_module_le_moved_sup_alpha_fixed
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (E : Subgroup G)
    (hfix : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ E) :
    U ≤ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔ (E ⊓ centralizer (pResidual 2 G : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hJY := RankOneBaumann.thompson_image_le_offender_layer T U q hq hker hUT Y le_rfl
  have hRY : (pResidual 2 G).map q ≤ Y := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact (offender_generation (T.mapSurjective hq) hp α hff hcore).1
  have hs := source_offender_pair_moved_sup_fixed α (T.mapSurjective hq) hp hff hcore d
  rw [← map_pResidual_of_surjective 2 q hq] at hs
  exact NormalElementaryQuotient.le_commutator_sup_fixed_of_generation U q hq hker
    (elementaryAbelianMaxJ (T : Subgroup G)) (pResidual 2 G) E Y hJY hRY hs hfix

private theorem paired_orbit_span_module_of_source_model
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  apply RankOneBaumann.paired_layer_thompsonAlpha_orbit_span T hP U hU hJ q hq hker
    Y c.action.groupEquiv c.quotientMap c.quotientMap_surjective
    (fun g v => c.quotientMap_action g v) ?_ le_rfl ?_
  · rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (T.mapSurjective hq) hp hff hcore F c
  · obtain ⟨t,h₁,h₂⟩ := hexchange
    have ht : (t:H) ∈ (T:Subgroup G).map q := t.property
    obtain ⟨g,hg,he⟩ := ht
    have hm₁ := congrArg (map Y.subtype) h₁
    have hm₂ := congrArg (map Y.subtype) h₂
    have hc : Y.subtype.comp (MulAut.conjNormal (t:H)).toMonoidHom =
        (MulAut.conj (t:H)).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [map_map,hc,← map_map] at hm₁ hm₂
    refine ⟨g,hg,?_,?_⟩
    · rw [← map_map,c.first_eq,← map_map,c.second_eq,he]
      exact hm₁
    · rw [← map_map,c.second_eq,← map_map,c.first_eq,he]
      exact hm₂


theorem paired_orbit_span_of_source_model
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  have hspan := paired_orbit_span_module_of_source_model T hP U hU hJ q hq hker d F c hexchange
  have hα := (paired_baumann_of_source_model T hP U hU hJ q hq hker d F c hexchange).2
  have hfix : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      thompsonAlpha (T : Subgroup G) := le_sup_right.trans hα.ge
  rw [hspan]
  exact le_antisymm
    (sup_le (paired_module_le_moved_sup_alpha_fixed T hP U hU hJ q hq hker d _ hfix) le_sup_right)
    (sup_le_sup_right (commutator_le_left _ _) _)
end CFSG.Quasithin.ChapterE.ThompsonAction
