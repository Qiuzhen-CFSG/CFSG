module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Stellmacher.SectionTwo.QuotientOffenders
public import Stellmacher.SectionOne.OneSevenDerivedElementary
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Extending a local solvable alternating block to the ambient group

The original elementary Thompson subgroup places the image of the chosen
local block in the canonical product of SL₂(2) factors on the actual global
Section Two module. Two-perfection places that image in the elementary
abelian derived product. The two-layer centralizer theorem and relative
subnormal core action show that the kernel normalizes the same block; its
subnormality therefore lifts. No change of block or quotient action occurs.

This is the solvable ambient extension in the C.1.29 pushing-up argument,
Aschbacher–Smith, combined manuscript (1 March 2004), printed pp.132–134.
The local minimal-parabolic construction supplies the explicit local block
hypotheses; the complete C.1/C.2 source route is unchanged.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.RankOne.Solvable
universe u

private theorem local_vSubgroup_le {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) :
    (Stellmacher.SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype ≤
      Stellmacher.SectionTwo.vSubgroup T := by
  let V := Stellmacher.SectionTwo.vSubgroup T
  let : V.Normal := Subgroup.normalClosure_normal
  apply map_le_iff_le_comap.mpr
  apply normalClosure_le_normal
  apply map_le_iff_le_comap.mp
  have hm : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  change (Stellmacher.omegaOneCenterAmbient _).map H.subtype ≤ V
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hm]
  exact le_normalClosure

private theorem blockU_map_equiv {B K : Type u} [Group B] [Group K]
    (e : B ≃* K) : (blockU B).map e.toMonoidHom = blockU K := by
  rw [blockU, blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective]

private theorem local_core_action {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal)
    (hpK : IsPPerfect 2 K) (Q : Subgroup G) [Q.Normal]
    (hQH : Q ≤ H) (hpQ : IsPGroup 2 Q) :
    Q ≤ normalizer K ∧ ⁅Q, K⁆ ≤ (blockU K).map K.subtype := by
  let B := K.subgroupOf H
  let R := Q.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hKH
  have hpB : IsPPerfect 2 B := hpK.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hpR : IsPGroup 2 R := hpQ.comap_subtype
  have hn := le_normalizer_of_isSubnormal_isPPerfect B R hsub hpB hpR
    le_normalizer_of_normal
  have hc := commutator_le_core_commutator_of_isSubnormal B R hsub hpB hpR
    le_normalizer_of_normal
  have hmB : B.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hmR : R.map H.subtype = Q := map_subgroupOf_eq_of_le hQH
  constructor
  · have hh := (map_mono (f := H.subtype) hn).trans (B.le_normalizer_map H.subtype)
    rwa [hmB, hmR] at hh
  · have hh := map_mono (f := H.subtype) hc
    rw [map_commutator, hmR, hmB] at hh
    have he : H.subtype.comp B.subtype = K.subtype.comp e.toMonoidHom := rfl
    change ⁅Q, K⁆ ≤ ((blockU B).map B.subtype).map H.subtype at hh
    rw [map_map, he, ← map_map, blockU_map_equiv] at hh
    exact hh

private theorem product_square_mem_derived
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : Stellmacher.IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, Stellmacher.SectionOne.IsOneSevenFactor (V := V) D) :
    ∀ e : E, (e : G) ^ 2 ∈ (commutator E).map E.subtype := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let P := ∀ i : I, (i : Subgroup G)
  have hcomm : Pairwise (fun i j : I => ∀ x y : G,
      x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2.2 i i.property j j.property
      (fun heq => hij (Subtype.ext heq)) x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := Subgroup.noncommPiCoprod_range |>.trans hprod.1.symm
  intro e
  obtain ⟨a, ha⟩ := show (e : G) ∈ f.range from hf ▸ e.property
  rw [← ha, ← map_pow]
  change f (a ^ 2) ∈ (commutator E).map E.subtype
  rw [Subgroup.noncommPiCoprod_apply]
  apply Subgroup.noncommProd_mem
  intro i _
  have hcardD : Nat.card (commutator (i : Subgroup G)) = 3 := by
    rw [← Subgroup.card_map_of_injective (i : Subgroup G).subtype_injective]
    exact (hF i i.property).2.1.2.1
  have hcardQ : Nat.card ((i : Subgroup G) ⧸ commutator (i : Subgroup G)) = 2 := by
    have hh := (commutator (i : Subgroup G)).index_mul_card
    rw [Subgroup.index_eq_card, hcardD,
      Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
        (hF i i.property).1] at hh
    omega
  have hsquare : a i ^ 2 ∈ commutator (i : Subgroup G) := by
    have hh := pow_card_eq_one' (x := QuotientGroup.mk' (commutator (i : Subgroup G)) (a i))
    rw [hcardQ, ← map_pow] at hh
    exact (QuotientGroup.eq_one_iff _).mp hh
  have hiE : (i : Subgroup G) ≤ E := by
    rw [hprod.1]
    exact le_iSup (fun j : I => (j : Subgroup G)) i
  have hder : (commutator (i : Subgroup G)).map (i : Subgroup G).subtype ≤
      (commutator E).map E.subtype := by
    rw [map_subtype_commutator, map_subtype_commutator]
    exact commutator_mono hiE hiE
  exact hder (mem_map_of_mem (i : Subgroup G).subtype hsquare)

private theorem twoPerfect_in_canonical_product_subnormal
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Stellmacher.SectionOne.Hypotheses G V) (S : Sylow 2 G)
    (K : Subgroup G) (hK : IsPPerfect 2 K)
    (hKE : K ≤ Stellmacher.SectionOne.oneSevenGenerated (G := G) (V := V)) :
    K.IsSubnormal := by
  let E := Stellmacher.SectionOne.oneSevenGenerated (G := G) (V := V)
  let F := Stellmacher.SectionOne.oneSevenFactors (G := G) (V := V)
  let R := (commutator E).map E.subtype
  obtain ⟨hEn, hprod, _⟩ := Stellmacher.SectionOne.oneSeven_global_product h S
  let : E.Normal := hEn
  let : R.Normal := by
    dsimp only [R]
    rw [map_subtype_commutator]
    infer_instance
  let : IsElementaryAbelian 3 R := Stellmacher.SectionOne.oneSeven_derived_isElementaryAbelian h
  have hsquare := product_square_mem_derived E F hprod
    (fun D hD => (Stellmacher.SectionOne.mem_oneSevenFactors_iff D).mp hD)
  have hp : IsPGroup 2 (E ⧸ commutator E) := by
    intro x
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (commutator E) x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨d, hd, he⟩ := hsquare e
    exact (Subtype.ext he : d = e ^ 2) ▸ hd
  have hres : pResidual 2 E ≤ commutator E := sInf_le ⟨inferInstance, hp⟩
  have hpKE : IsPPerfect 2 (K.subgroupOf E) :=
    hK.of_surjective (subgroupOfEquivOfLe hKE).symm.toMonoidHom
      (subgroupOfEquivOfLe hKE).symm.surjective
  have hKR : K ≤ R := by
    have hh := map_mono (f := E.subtype)
      ((le_pResidual_of_isPPerfect (K.subgroupOf E) hpKE).trans hres)
    rwa [map_subgroupOf_eq_of_le hKE] at hh
  exact IsSubnormal.step K R hKR (inferInstance : R.Normal).isSubnormal inferInstance

private theorem quotient_block_subnormal {G : Type u} [Group G] [Finite G]
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (K : Subgroup G) (hpK : IsPPerfect 2 K)
    (hJ : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    {B : Type u} [Group B] [Finite B] (q : G →* B) (hq : Function.Surjective q)
    (hker : q.ker = Stellmacher.SectionTwo.cSubgroup T) :
    (K.map q).IsSubnormal := by
  let V := Stellmacher.SectionTwo.vSubgroup T
  let : IsElementaryAbelian 2 V :=
    (Stellmacher.SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h T).2
  let := Stellmacher.SectionTwo.quotientConjugationAction T q hq hker
  let S := T.mapSurjective hq
  let J := Stellmacher.SectionOne.oneJ (V := V) (S : Subgroup B)
  have hmax : (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ J :=
    Stellmacher.SectionTwo.elementaryAbelianMaxJ_map_le_oneJ h T q hq hker
  have hKcomm : K.map q = ⁅K.map q,
      (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).map q⁆ := by
    rw [← map_commutator, ← hJ]
  by_cases hJbot : J = ⊥
  · have hb := bot_unique (hJbot ▸ hmax)
    rw [hKcomm, hb, commutator_bot_right]
    exact IsSubnormal.bot
  have hJS : J ≤ (S : Subgroup B) := sSup_le fun A hA => hA.1
  have hSne : (S : Subgroup B) ≠ ⊥ := by
    intro hb
    exact hJbot (bot_unique (hb ▸ hJS))
  have htwo : 2 ∣ Nat.card S := S.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hone => hSne (Subgroup.card_eq_one.mp hone))
  let : Group.IsSolvable G := h.solvable
  have hOne : Stellmacher.SectionOne.Hypotheses B V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (htwo.trans (S : Subgroup B).card_subgroup_dvd_card),
      Stellmacher.SectionTwo.quotientConjugationAction_faithful T q hq hker,
      Stellmacher.SectionTwo.lemma_two_one h T q hq hker⟩
  obtain ⟨hEn, _, hJE⟩ := Stellmacher.SectionOne.oneSeven_global_product hOne S
  let E := Stellmacher.SectionOne.oneSevenGenerated (G := B) (V := V)
  let : E.Normal := hEn
  have hKE : K.map q ≤ E := by
    rw [hKcomm]
    exact (commutator_mono le_rfl (hmax.trans hJE)).trans (commutator_le_right _ _)
  exact twoPerfect_in_canonical_product_subnormal hOne S (K.map q)
    (hpK.of_surjective (q.subgroupMap K) (q.subgroupMap_surjective K)) hKE

/-- The same locally subnormal A₃ block is subnormal in the ambient group.
The support hypothesis is on the original local Section Two module. -/
public theorem isSubnormal_of_local_alternatingThree
    {G : Type u} [Group G] [Finite G]
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    {H K : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (ha : IsAlternatingBlock K 3)
    (hJ : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hU : (blockU K).map K.subtype ≤
      (Stellmacher.SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype) :
    K.IsSubnormal := by
  let Q := pCore 2 G
  let V := Stellmacher.SectionTwo.vSubgroup T
  let C := centralizer (V : Set G)
  let : Q.Normal := pCore_normal
  let : V.Normal := normalClosure_normal
  let : C.Normal := inferInstance
  let : IsElementaryAbelian 2 V :=
    (Stellmacher.SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h T).2
  have hpK : IsPPerfect 2 K := ha.2.1.twoPerfect
  have hQH : Q ≤ H := (fitting_pCore_le_sylow T).trans hTH
  obtain ⟨hQK, hcomm⟩ := local_core_action hKH hsub hpK Q hQH pCore_isPGroup
  have hUV : (blockU K).map K.subtype ≤ V := hU.trans (local_vSubgroup_le T hTH)
  have hKQ : ⁅K, Q⁆ ≤ V := by
    rw [commutator_comm]
    exact hcomm.trans hUV
  let D := commutatorPreimage ⊤ Q V
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (commutatorPreimage_normalized ⊤ Q V ⊤
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal)
  have hKD : K ≤ D := le_commutatorPreimage le_top hKQ
  have hCQ : ⁅C, K⁆ ≤ Q :=
    (le_inf (commutator_le_left _ _)
      ((commutator_mono le_rfl hKD).trans (commutator_le_right _ _))).trans
      (two_layer_le_radical Q V Q
        (IsElementaryAbelian.isPGroup 2 V)
        (pCore_quotient_pCore_eq_bot 2)
        (inf_le_right.trans h.centralizer_twoCore_le))
  let X := K ⊔ Q
  have hKX : K ≤ X := le_sup_left
  have hQX : Q ≤ X := le_sup_right
  let : (K.subgroupOf X).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hQK)
  have hpKX : IsPPerfect 2 (K.subgroupOf X) :=
    hpK.of_surjective (subgroupOfEquivOfLe hKX).symm.toMonoidHom
      (subgroupOfEquivOfLe hKX).symm.surjective
  have hres : (pResidual 2 X).map X.subtype = K := by
    rw [pResidual_eq_of_isPPerfect_sup (K.subgroupOf X) (Q.subgroupOf X)
      hpKX (pCore_isPGroup (p := 2) (G := G)).comap_subtype
      (codisjoint_subgroupOf_sup K Q).eq_top,
      map_subgroupOf_eq_of_le hKX]
  have hCX : C ≤ normalizer X :=
    le_normalizer_sup_of_commutator_le K C K Q le_rfl
      (by rwa [commutator_comm])
  have hCK : C ≤ normalizer K := by
    rw [← hres]
    exact hCX.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
  let q := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = Stellmacher.SectionTwo.cSubgroup T := QuotientGroup.ker_mk' C
  have hqK := quotient_block_subnormal h T K hpK hJ q hq hker
  have hsup : (K ⊔ C).IsSubnormal := by
    have hh := hqK.comap q
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at hh
  exact IsSubnormal.step K (K ⊔ C) le_sup_left hsup
    (normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hCK))

/-- Literal outside-block consumer: the chosen local subgroup remains the
same ambient alternating block, with its original quotient and module model. -/
public theorem outside_block_of_local_alternatingThree
    {G : Type u} [Group G] [Finite G]
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    {H K M : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (ha : IsAlternatingBlock K 3)
    (hJ : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hU : (blockU K).map K.subtype ≤
      (Stellmacher.SectionTwo.vSubgroup (T.subtype hTH)).map H.subtype)
    (hout : ¬ K ≤ M) : ¬ K ≤ M ∧ IsBlock K ∧ IsAlternatingBlock K 3 :=
  ⟨hout, ⟨inferInstance, ha.2.1,
    isSubnormal_of_local_alternatingThree h T hTH hKH hsub ha hJ hU⟩, ha⟩

end CFSG.Quasithin.ChapterC.RankOne.Solvable
