module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.NormalImage
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.GroupTheory.ProjectedModuleAbsorption
/-!
# The residual four-group in the secondary component

For the single alternating-five block on printed pp.545–546, the residual
alternating-four actor acts faithfully on the selected component. If its marked
involution acts internally, its elementary four-group belongs to that component:
the projected module argument lifts the inner image using the actual Sylow
normalizer index at most two. The original marked involution then gives component
normality, the full layer, and the generalized Fitting subgroup.

The final consumer constructs the original 1.1.5 input from the selected secondary
centralizer; it retains the precise finite geometry and model-innerness inputs.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC
private theorem cubic_block_of_equiv
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (e : A ≃* alternatingGroup (Fin 4)) :
    IsAlternatingBlock A 3 ∧ pCore 2 A = blockU A := by
  let eC : pCore 2 A ≃* pCore 2 (alternatingGroup (Fin 4)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hc : Nat.card (pCore 2 A) = 4 := by
    rw [Nat.card_congr eC.toEquiv,AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have he4 : IsElementaryAbelian 2 (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
    exact { toIsMulCommutative := hk.isMulCommutative
            exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let := he4
  have he : IsElementaryAbelian 2 (pCore 2 A) :=
    IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
  have hq : Nat.card (A ⧸ pCore 2 A) = 3 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [hc,Nat.card_congr e.toEquiv,alternatingGroup.card_of_card_eq_four (by norm_num)] at hh
    omega
  have hb := ChapterC.RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hp he hc hq
  exact ⟨hb,hb.2.1.core_eq_blockU_of_quotient_three hq⟩


variable {G : Type*} [Group G] [Finite G]

theorem secondary_component_core_le_of_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u}:Set G)) P M z)
    (L R K : Subgroup (centralizer ({u}:Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u}:Set G)) K)
    (e : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=(a:G)*u)
    (hzK : center K=⊥)
    (hinner : (K.normalizerMonoidHom.comp
      (inclusion (secondary_component_residual_normalizes hG u hu L K hL hK))) a
        ∈ MulAut.innerSubgroup K)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2) :
    (pCore 2 L).map L.subtype ≤ K := by
  let C := centralizer ({u}:Set G)
  let N := normalizer (K : Set C)
  let KN := K.subgroupOf N
  let LN := L.subgroupOf N
  let E := (pCore 2 L).map L.subtype
  let EN := E.subgroupOf N
  have hLN : L ≤ N := secondary_component_residual_normalizes hG u hu L K hL hK
  have hEL : E ≤ L := map_subtype_le _
  have hEN : E ≤ N := hEL.trans hLN
  let j : L →* N := inclusion hLN
  let φ := K.normalizerMonoidHom
  let f := φ.comp j
  have hf : Function.Injective f :=
    (secondary_component_faithful_residual_action hG u hu P M z h115 L K hL hK e a ha hz).1
  have hφL : Function.Injective (φ.comp LN.subtype) := by
    intro l m he
    apply (subgroupOfEquivOfLe hLN).injective
    exact hf he
  have hφK : Function.Injective (φ.comp KN.subtype) := by
    have bridge (k : KN) : φ (k:N)=MulAut.conj ((subgroupOfEquivOfLe K.le_normalizer) k) := by
      apply MulEquiv.ext
      intro x
      rfl
    intro a b he
    exact (subgroupOfEquivOfLe K.le_normalizer).injective
      (conj_injective_of_center_eq_bot hzK ((bridge a).symm.trans (he.trans (bridge b))))
  obtain ⟨hb,hcore⟩ := cubic_block_of_equiv hL e
  have hna : a≠1 := by
    intro he
    have hz1 : z=u := by rw [he] at hz; simpa using hz
    obtain ⟨_,α,_,hα,mark,_⟩ := h115.component_inputs K hK
    have hα1 : α=1 := by
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      apply Subtype.ext
      rw [hα,hz1]
      exact by rw [←mem_centralizer_singleton_iff.mp (k:C).property,mul_inv_cancel_right]; rfl
    have hh := mark.order_two
    rw [hα1,orderOf_one] at hh
    norm_num at hh
  have him : EN.map φ ≤ KN.map φ := by
    have hi := hb.module_image_le_normal_of_nontrivial f (MulAut.innerSubgroup K)
      a (hcore ▸ ha) hna hinner
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hew⟩ := hv
    have hj : j w=v := by
      apply Subtype.ext
      exact hew
    have hii := hi (mem_map_of_mem f (hcore ▸ hw))
    change f w ∈ (MulAut.conj : K →* MulAut K).range at hii
    rw [show f w=φ v from congrArg φ hj] at hii
    obtain ⟨k,hk⟩ := hii
    refine ⟨⟨k,K.le_normalizer k.property⟩,k.property,?_⟩
    have hφk : φ ⟨k,K.le_normalizer k.property⟩=MulAut.conj k := by
      apply MulEquiv.ext
      intro x
      rfl
    exact hφk.trans hk
  obtain ⟨Q,hQ,_⟩ := secondary_component_residual_action_normalizer_bound hG u hu P L R K hL hK hRL hri
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  obtain ⟨QK,hQK⟩ := Q.exists_subgroupOf_eq_of_normal KN
  have hQKS : (QK : Subgroup KN).map KN.subtype ≤ (Q : Subgroup N) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [hQK] at hx
    exact hx
  have hES : EN ≤ (Q : Subgroup N) := by
    rw [hQ]
    exact fun _ hx => hEP hx
  have hc : ⁅EN,LN⁆=EN := by
    have hc0 : ⁅E,L⁆=E := by
      have hi := commutator_isPPerfect_idempotent L (pCoreIn 2 L)
        hL (isPGroup_pCoreIn 2 L)
        (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      have hh : ⁅(blockU L).map L.subtype,L⁆=(blockU L).map L.subtype := by
        simpa only [pCoreIn,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hi
      rw [←hcore] at hh
      exact hh
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEN,map_subgroupOf_eq_of_le hLN,hc0]
  have hidx : (normalizer (LN : Set N)).relIndex (Q : Subgroup N)≤2 := by
    have hRN : R.subgroupOf N≤normalizer (LN : Set N) := by
      rw [show LN=L.subgroupOf N from rfl,←subgroupOf_normalizer_eq hLN]
      exact comap_mono hRL
    apply (relIndex_le_of_le_left hRN index_ne_zero_of_finite).trans
    rw [hQ]
    change (R.comap N.subtype).relIndex ((P : Subgroup C).subgroupOf N)≤2
    rw [relIndex_comap]
    exact (relIndex_le_of_le_right (show ((P : Subgroup C).subgroupOf N).map N.subtype≤(P : Subgroup C) from by
      rintro _ ⟨x,hx,rfl⟩; exact hx) index_ne_zero_of_finite).trans hri
  let : IsElementaryAbelian 2 E := (hcore ▸ hb.2.1.elementary).map L.subtype
  let : IsElementaryAbelian 2 EN := IsElementaryAbelian.subgroupOf hEN
  have hh : EN≤KN := module_le_normal_factor_of_image KN LN EN Q φ hφK hφL
    (fun _ hx=>hEL hx) hES Q.isPGroup' QK hQKS hc him hidx
  intro x hx
  exact hh (show (⟨x,hEN hx⟩ : N)∈EN from hx)

theorem secondary_component_structure_of_inner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u}:Set G)) P M z)
    (L R K : Subgroup (centralizer ({u}:Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u}:Set G)) K)
    (e : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=(a:G)*u)
    (hzK : center K=⊥)
    (hinner : (K.normalizerMonoidHom.comp
      (inclusion (secondary_component_residual_normalizes hG u hu L K hL hK))) a
        ∈ MulAut.innerSubgroup K)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2)
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥) :
    K.Normal ∧ K=componentLayer (centralizer ({u}:Set G)) ∧
      generalizedFitting (centralizer ({u}:Set G))=K ⊔ pCore 2 (centralizer ({u}:Set G)) := by
  have hE := secondary_component_core_le_of_inner hG u hu P M z h115 L R K hL hK
    e a ha hz hzK hinner hEP hRL hri
  exact DoubleA3.source_component_structure u P M z h115 K hK (a : centralizer ({u}:Set G))
    (hE (mem_map_of_mem L.subtype ha)) hz ho

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
include hG hu in
theorem MinimalBlockSetup.single_alternating_secondary_component_structure_of_marks
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N=M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
    (hout : ¬d.H ⊓ centralizer ({u}:Set G) ≤ M)
    (hMu : M ⊓ centralizer ({u}:Set G)=(T : Subgroup G) ⊓ centralizer ({u}:Set G))
    (hi : ((T : Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T : Subgroup G)=2)
    (P : Sylow 2 (centralizer ({u}:Set G)))
    (hP : (P : Subgroup (centralizer ({u}:Set G))).map (centralizer ({u}:Set G)).subtype=
      (T : Subgroup G) ⊓ centralizer ({u}:Set G))
    (z : G) (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
    (hz2 : orderOf z=2)
    (L R K : Subgroup (centralizer ({u}:Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u}:Set G)) K)
    (e : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hza : z=(a:G)*u)
    (hzK : center K=⊥)
    (hinner : (K.normalizerMonoidHom.comp
      (inclusion (secondary_component_residual_normalizes hG u hu L K hL hK))) a
        ∈ MulAut.innerSubgroup K)
    (hEP : (pCore 2 L).map L.subtype ≤ (P : Subgroup (centralizer ({u}:Set G))))
    (hRL : R ≤ normalizer (L : Set (centralizer ({u}:Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u}:Set G))) ≤ 2)
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥) :
    K.Normal ∧ K=componentLayer (centralizer ({u}:Set G)) ∧
      generalizedFitting (centralizer ({u}:Set G))=K ⊔ pCore 2 (centralizer ({u}:Set G)) := by
  have h115 := d.single_alternating_secondary_lemma115_of_marks hG T hM hTM hunique hST
    hsingle hA u hu huR hout hMu hi P hP z hz hz2
  exact secondary_component_structure_of_inner hG u hu P M z h115 L R K hL hK e a ha hza
    hzK hinner hEP hRL hri ho

end CFSG.Quasithin.Chapter2
