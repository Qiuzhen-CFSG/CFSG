module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SeedControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.OriginalSection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FivePairControl

/-!
# Source moved-section coordinates with Baumann control

The actual B.5.1 moved section gives the literal quotient map and its
centralizer kernel. The seed comparison then feeds the universal Baumann
pair using only characteristic-normalizer control of Baum(T). No full-Sylow
control or replacement of the original seed is required. For the separate
A₅ row, the first pair member remains nontrivial after restriction to Z(T).

Source: Aschbacher--Smith C.1.19, C.1.26 and 15.1.20(2),
printed pp.127,132,1094--1095.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u v
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
/-- The B.5.1 moved section supplies the natural marker on the original
seed; Baumann control eliminates the pair alternatives. -/
theorem quasisimple_linear_seed_chi_of_baumann_control
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
    (hseed : U ≤ normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (M : Subgroup G)
    (hcpu : (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M)
    (hout : ¬ pResidual 2 G ≤ M) : IsChiBlockIn (pResidual 2 G) := by
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
  apply normal_layer_seed_block_of_baumann_control T hP U hU hJ q hq hker
    L eg hF (sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e)
    (sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e) ?_
    (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e)
    hseed hfit M hcpu hout
  intro g hg v
  let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
  have ha : q g = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
  exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v


open GlaubermanNiles FiveBlockSource
/-- The canonical center restriction of the first pair member is nontrivial. -/
theorem firstAmbient_ne_bot (T : Subgroup G) (hp : IsPGroup 2 T)
    (D : CharacteristicPair (baumann T)) :
    firstAmbient T D ≠ ⊥ := by
  let B := (baumann T).subgroupOf T
  have hB : B = baumann (⊤ : Subgroup T) := by
    apply map_injective T.subtype_injective
    rw [map_subgroupOf_eq_of_le (show baumann T ≤ T from inf_le_left)]
    symm
    change ((⊤ : Subgroup T) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (⊤ : Subgroup T)) : Set T)).map T.subtype = _
    rw [baumann_map_injective T.subtype T.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  let : B.Characteristic := hB ▸ baumann_characteristic
  let a : baumann T ≃* B := (subgroupOfEquivOfLe (show baumann T ≤ T from inf_le_left)).symm
  let E := transportPair D a
  let : E.first.Characteristic := E.first_characteristic
  have hc := centerRestriction_spec hp B E.first E.first_ne_bot E.first_le_omegaCenter
  let : (centerRestriction B E.first).Characteristic := hc.1
  have hm : (centerRestriction B E.first).map T.subtype = firstAmbient T D := by
    change (center T ⊓ E.first.map B.subtype).map T.subtype = _
    rw [Subgroup.map_inf _ _ _ T.subtype_injective,map_map]
    change (center T).map T.subtype ⊓ (D.first.map a.toMonoidHom).map _ = _
    rw [map_map]
    rfl
  rw [←hm]
  exact fun hz => hc.2.1 (((centerRestriction B E.first).map_eq_bot_iff_of_injective
    T.subtype_injective).mp hz)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
