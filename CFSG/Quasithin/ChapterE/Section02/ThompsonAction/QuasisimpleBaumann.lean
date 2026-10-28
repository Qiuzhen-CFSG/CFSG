module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.RankOne
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification
/-!
# Genuine single-quasisimple natural Baumann source application

The original normal offender supplement has its quasisimple generalized
Fitting subgroup equal to the original residual image. Its actual moved
central quotient supplies the natural coordinates on [U,O²(H)], with the
literal residual-centralizer kernel and ambient conjugation. Perfectness
excludes the binary field of order two. The normal-layer Baumann theorem
therefore gives the original Sylow conclusion and the exact moved-alpha
identity. The source row selector leaves only the marked symmetric-five
case for its separate C.1.24 argument.

Source: Aschbacher–Smith B.6.9–10 and E.2.3, pp.115–117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
/-- A nontrivial perfect natural SL₂ actor has field order greater than two. -/
theorem perfect_linear_two_field_large {A : Type*} [Group A] [Group.IsPerfect A]
    [Nontrivial A] (F : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    2 < Nat.card F.Carrier := by
  by_contra hn
  have hd : F.degree = 1 := by
    have hdpos := F.degree_pos
    have hn' : 2^F.degree ≤ 2 := by simpa only [F.card_eq] using Nat.le_of_not_gt hn
    by_contra h
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    norm_num at hpow
    omega
  let c := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable A
    (Group.isSolvable_of_surjective (f := c.symm.toMonoidHom) c.symm.surjective)

attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_linear_baumann_of_section
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
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
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
  apply RankOneBaumann.normal_layer_moved_baumann_sylow_and_alpha T hP U hU hJ q hq hker
    L eg hF (sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e)
    (sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e) ?_
    (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e)
  intro g hg v
  let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
  have ha : q g = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
  exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v

/-- Genuine source recognition discharges the natural marker in the original
quasisimple branch; the marked symmetric-five row remains for C.1.24. -/
theorem quasisimple_baumann_or_symmetric_five
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))) :
    let α := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup α
    (Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G))) ∨
      Nonempty (MarkedActionEquiv c.sectionData.action
        (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) := by
  let α := NormalElementaryQuotient.representation U q hq hker
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
  rcases source_offender_quasisimple_rank_one α (T.mapSurjective hq) hp hff hcore hqs c with
    ⟨F,hF⟩ | hs
  · exact Or.inl (quasisimple_linear_baumann_of_section T hP U hU hJ q hq hker hqs c.sectionData F hF)
  · exact Or.inr hs
end CFSG.Quasithin.ChapterE.ThompsonAction
