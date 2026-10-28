module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NaturalOrbitSpan
/-!
# The original quasisimple branch gives the E.2.3 orbit span

The same actual B.5.1 moved section supplies the natural quotient on
[U,O²(H)], with its literal residual-fixed kernel. The sharp two-conjugate
calculation therefore identifies the orbit of alpha under the original
residual. No additional splitting, generation or fixed-space premise is used.
Source: Aschbacher–Smith E.2.3(2), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_linear_orbit_span_of_section
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
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
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.groupEquiv
  apply RankOneBaumann.normal_layer_moved_thompsonAlpha_orbit_span T hP U hU hJ q hq hker
    L eg hF (sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e)
    (sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e) ?_
    (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e)
  intro g hg v
  let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
  have ha : q g = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
  exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v

end CFSG.Quasithin.ChapterE.ThompsonAction
