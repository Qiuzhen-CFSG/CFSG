module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SourceLocal
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentSelection
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
/-!
# The single natural E.2.3 source is an actual C.1.17 component

Lift the original quasisimple residual image through its reduced-action
centralizer. The canonical component is normal, supplements the prescribed
Sylow, and hence equals the actual two-residual. Its same moved-section
coordinates give the natural local class and exact localV identity.

Source: Aschbacher--Smith C.1.26 and E.2.3, printed pp.132 and216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem quasisimple_linear_component_localClass
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
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
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (hs : ¬ Group.IsSolvable G)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    let B := baumann (T : Subgroup G)
    let R := pResidual 2 G
    R.IsCComponent ∧
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ R ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ R ⊔ B from le_sup_right))).map (R ⊔ B).subtype =
        (⁅U,R⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (R : Set G)) := by
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
  have hLc : IsComponent H L :=
    ⟨(inferInstance : L.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (A.equivMapOfInjective Y.subtype Y.subtype_injective)⟩
  obtain ⟨K,hK,hKm,_,_,hcan⟩ := exists_component_with_intrinsic_frattini_kernel
    h36 hG T hP U hU hJ q hq hker hs L hLc
  have hNK : (⊤ : Subgroup G) ≤ normalizer (K : Set G) :=
    selected_component_normalized q L K ⊤ hcan (by rw [normalizer_eq_top]; exact le_top)
  let : K.Normal := normalizer_eq_top_iff.mp (top_unique hNK)
  have hKT : K ⊔ (T : Subgroup G) = ⊤ := by
    obtain hb | hb := minimalParabolic_normal_subgroup_dichotomy T hP K
    · let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
      exact (hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb))).elim
    · simpa only [sup_comm] using hb
  let : Group.IsPerfect K := hK.perfect
  have hr : pResidual 2 G = K := (residuals_of_perfect_normal_sup_twoGroup K
    (T : Subgroup G) T.isPGroup' hKT).1
  have hR : (pResidual 2 G).IsCComponent := hr.symm ▸ hK
  let fv := sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e
  have hfv := sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e
  have hkv := sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e
  have hev : ∀ (g : G) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      fv (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        SL2NaturalOffenders.NoStrong.natural (eg ⟨q g,hg⟩) (fv v) := by
    intro g hg v
    let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
    have ha : q g = (a:Y) := (congrArg Subtype.val
      ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
    exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v
  exact ⟨hR,normal_layer_selected_localClass T hP U hU hJ q hq hker L eg hF
      fv hfv hev hkv hspan hfit,
    (normal_layer_selected_geometry T hP U hU hJ q hq hker L eg hF
      fv hfv hev hkv hspan hfit).2.2.2.2⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
