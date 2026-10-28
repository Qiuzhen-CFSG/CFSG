module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSource
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The original doubled-natural module centralizes J₁(T)

The original faithful reduced action has kernel O₂(LT). Its component
image is the actual L/O₂(L), and its quotient is a two-group. Consequently
the component centralizer is trivial. Transporting the supplied doubled
natural coordinates through these literal maps lets the near-maximum
inequality prove that J₁(T) fixes the original module.

This constructs the Thompson-centralization step of the doubled row in
source 6.1.4; neither a quotient-rank nor a centralizer bound is assumed.
-/
set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- A genuine doubled-natural marking forces the original higher Thompson
subgroup to centralize W, through the original LT two-core quotient. -/
theorem Input.thompson_one_centralizes_of_doubled_natural
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (F : BinaryField) (hF : F.degree = n)
    (hm : IsConjugationModel L W (repeated (linearNatural F 2) 2)) :
    ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (W : Set G) := by
  obtain ⟨e0,f0,hf0⟩ := hm
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let B := L.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let Q := M ⧸ pCore 2 M
  let q : M →* Q := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set M) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let Bq := B.map q
  let : Bq.Normal := (inferInstance : B.Normal).map q hq
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
  let eB : Bq ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier :=
    (coreQuotientEquivImage 2 B).symm.trans
      ((QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)).trans e0)
  have hsup : B ⊔ (S : Subgroup M) = ⊤ := by
    change L.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤
    rw [←subgroupOf_sup (show L ≤ M from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 (Q ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq ((S : Subgroup M).map q) (S.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center Bq = ⊥ := by
    apply bot_unique
    intro x hx
    apply eB.map_eq_one_iff.mp
    exact (Theory.PSL2.sl2_center_eq_bot F.Carrier).le
      (MulEquivClass.apply_mem_center eB hx)
  have hC : centralizer (Bq : Set Q) = ⊥ := by
    have hp := centralizer_isPGroup_of_centerless_quotient Bq hz htwo
    have hc : centralizer (Bq : Set Q) ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
    exact bot_unique (hc.trans_eq (pCore_quotient_pCore_eq_bot (G:=M) 2))
  let uW : U ≃* W := subgroupOfEquivOfLe h.reduced.1
  let f := uW.trans f0
  let c : Additive U ≃ₗ[ZMod 2] (Fin 2 → NaturalTensor.NaturalSpace F.Carrier) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  have hc : ∀ (l : Bq) x,
      c (NormalElementaryQuotient.representation U q hq hk l x) =
        NaturalTensor.naturalSumAction F.Carrier (Fin 2) (eB l) (c x) := by
    intro l x
    obtain ⟨b,hb⟩ := q.subgroupMap_surjective B l
    let l0 : L := eb b
    have heB : eB (q.subgroupMap B b) = e0 (QuotientGroup.mk' (pCore 2 L) l0) := by
      change e0 (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb _
        ((coreQuotientEquivImage 2 B).symm (q.subgroupMap B b))) = _
      have heq : coreQuotientEquivImage 2 B (QuotientGroup.mk' (pCore 2 B) b) =
          q.subgroupMap B b := by
        apply Subtype.ext
        exact coreQuotientEquivImage_apply_mk 2 B b
      rw [←heq,MulEquiv.symm_apply_apply]
      rfl
    subst l
    rw [heB]
    let v : W := uW x.toMul
    have hact := hf0 l0 v
    have hcoords := congrArg f0
      (show f0.symm (Multiplicative.ofAdd
        (repeated (linearNatural F 2) 2
          (e0 (QuotientGroup.mk' (pCore 2 L) l0)) (f0 v).toAdd)) =
        W.normalizerMonoidHom ⟨l0,(le_sup_left.trans (reduced_normalizes h.reduced)) l0.property⟩ v from
          Subtype.ext hact)
    rw [f0.apply_symm_apply] at hcoords
    change c (NormalElementaryQuotient.representation U q hq hk (q b.val) x) = _
    apply Eq.trans ?_ (congrArg Multiplicative.toAdd hcoords.symm)
    apply congrArg (fun w : W => (f0 w).toAdd)
    apply Subtype.ext
    change (((NormalElementaryQuotient.representation U q hq hk (q b.val) x).toMul : M) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  have hUS : U ≤ (S : Subgroup M) := h.reduced_internal.le_pCore.trans
    (pCore_isPGroup.le_sylow_of_normal S)
  have hTh := RankOneRecognition.doubled_natural_thompson_one_centralizes
    (S : Subgroup M) U hUS q hq hk Bq eB hC c hc h.exponent
      (hF ▸ F.card_eq)
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hUm : U.map M.subtype = W := map_subgroupOf_eq_of_le h.reduced.1
  rw [←hSm,ChapterB.thompsonJ_map_injective M.subtype M.subtype_injective]
  rintro x ⟨x,hx,rfl⟩ w hw
  obtain ⟨u,hu,rfl⟩ := hUm.symm ▸ hw
  exact congrArg M.subtype (hTh hx u hu)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
