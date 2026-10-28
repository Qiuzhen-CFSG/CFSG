module
public import Glauberman.BaumannClassTwoCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductNilesBinary

/-!
# The original root-product commutator conclusion

Retain the actual envelope F and its Baumann normal closure F₀. The original
Baumann Sylow has class two and elementary full center. Its Thompson-omega
enlargement has residual displacement in U-alpha, so normal generation and
residual idempotence put [O₂(F₀),O²(F₀)] in U-alpha. The original Q-alpha
normalizes F₀ inside F; its first residual commutator lies in O₂(F₀).
A second use of idempotence gives [Q-alpha,O²(F₀)] in U-alpha, hence Z-alpha.
All subgroups use their literal inclusions and the original field degree.

Source: MS93 (5.1), printed p.913, the consequence of Niles Theorem B.
The downstream RootProductExclusion uses this bound for the contradiction;
selected-path and terminal distance exclusions remain subsequent steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit NilesRankOneKernel
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_root_product_core_commutator
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical),
        I ≤ stabilizer d.radical a ∧ Q d.radical a ≤ I ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        (∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t)) ∧
        ⁅U d.radical a,(pResidual 2 C).map C.subtype⁆ ≠ ⊥ ∧
        ⁅Q d.radical a,(pResidual 2 C).map C.subtype⁆ ≤ U d.radical a ∧
        ⁅Q d.radical a,(pResidual 2 C).map C.subtype⁆ ≤ Z d.radical a := by
  obtain ⟨E,hE,I,hI,S,hS,hgen,⟨eN⟩,hfit,hres,P,hP,hunique,hOm,hBe,hDne,hDc,hZc⟩ :=
    h.replacement_root_product_baumann_sylow d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  let f := I.subtype.comp N.subtype
  have hf : Function.Injective f := I.subtype_injective.comp N.subtype_injective
  let B := Glauberman.baumannSubgroup (Q d.radical t)
  have hPB : (P : Subgroup N).map f = B := by rw [←Subgroup.map_map]; exact hP
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F ^ 2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hQI : Q d.radical a ≤ I := hQJ.trans (hS ▸ map_subtype_le _)
  obtain ⟨_,hWe,hWn,hWQ,hWL,_⟩ := h.replacement_root_product_thompson_layer
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let W := omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a
  let : IsElementaryAbelian 2 W := hWe
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hWB : W ≤ B := Glauberman.elementary_layer_le_baumann _ W (hWQ.trans hQT) le_sup_left
  have hWN : W ≤ N.map I.subtype := by
    apply hWB.trans
    change Glauberman.baumannSubgroup (Q d.radical t) ≤ _
    rw [←hP]
    exact map_mono (map_subtype_le _)
  have hWI : W ≤ I := hWQ.trans hQI
  have hUI : U d.radical a ≤ I := le_sup_right.trans hWI
  let U₁ := (U d.radical a).subgroupOf I
  let U₀ := U₁.subgroupOf N
  have hUN : U₁ ≤ N := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hWN ((show U d.radical a ≤ W from le_sup_right) hu)
    exact I.subtype_injective he ▸ hv
  have hUm : U₀.map f = U d.radical a := by
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hUN,map_subgroupOf_eq_of_le hUI]
  let : U₁.Normal := (normal_subgroupOf_iff_le_normalizer hUI).mpr (hI.trans (U_normalized a))
  let : U₀.Normal := inferInstance
  let W₁ := W.subgroupOf I
  let : W₁.Normal := (normal_subgroupOf_iff_le_normalizer hWI).mpr (hI.trans hWn)
  have hWN' : W₁ ≤ N := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hWN hu
    exact I.subtype_injective he ▸ hv
  let W₀ := omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊔ U₀
  have hWm : W₀.map f = W := by
    rw [Subgroup.map_sup,←Subgroup.map_map,hOm,hUm]
  have hWnative : W₀ = W₁.subgroupOf N := by
    apply map_injective hf
    rw [hWm,←Subgroup.map_map,map_subgroupOf_eq_of_le hWN',map_subgroupOf_eq_of_le hWI]
  let : W₀.Normal := hWnative ▸ inferInstance
  have hLm : (pResidual 2 N).map f = (pResidual 2 I).map I.subtype := by
    rw [←Subgroup.map_map,hres]
  have hmoveNe : ⁅U d.radical a,(pResidual 2 I).map I.subtype⁆ ≠ ⊥ := by
    intro hz
    apply hDne
    apply (map_eq_bot_iff_of_injective _ hf).mp
    rw [map_commutator,hUm,hLm,hz]
  have hLL : (pResidual 2 N).map f ≤ Ltilde d.radical a := by
    rw [hLm]
    exact embedded_pResidual_mono 2 hI
  have hmove : ⁅W₀,pResidual 2 N⁆ ≤ U₀ := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [map_commutator,hWm,hUm]
    exact (commutator_mono le_rfl hLL).trans hWL
  have hBclass := (h.replacement_root_product_baumann_class_two d geometry hb ha hat
    E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod).1
  have hclass : (P : Subgroup N).lowerCentralSeries 2 = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ hf).mp
    rw [map_lowerCentralSeries,hPB]
    exact hBclass
  have hBc := h.replacement_root_product_baumann_center d geometry hb ha hat
    E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hPc : omegaCenterIn (P : Subgroup N) = centerIn (P : Subgroup N) := by
    apply le_antisymm
    · intro z hz
      exact ⟨((mem_omegaCenterIn_iff _ _).mp hz).1,((mem_omegaCenterIn_iff _ _).mp hz).2.1⟩
    · intro z hz
      have hzc : f z ∈ centerIn B := by
        refine ⟨hPB ▸ mem_map_of_mem f hz.1,?_⟩
        intro y hy
        obtain ⟨w,hw,rfl⟩ := hPB.symm ▸ hy
        simpa only [map_mul] using congrArg f (hz.2 w hw)
      change f z ∈ centerIn (Glauberman.baumannSubgroup (Q d.radical t)) at hzc
      rw [←hBc] at hzc
      change f z ∈ omegaCenterIn B at hzc
      rw [←hPB,←Glauberman.omegaCenterIn_map_injective _ f hf] at hzc
      obtain ⟨w,hw,he⟩ := hzc
      exact hf he ▸ hw
  let r := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hr : Function.Surjective r := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrk : r.ker = pCore 2 N := by
    rw [MonoidHom.ker_comp_of_injective _ _ eN.injective,QuotientGroup.ker_mk']
  obtain ⟨x,hx,hpair,hinter⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair r hr hrk P
  have hPgen : normalClosure ((P : Subgroup N) : Set N) = ⊤ := by
    apply top_unique
    rw [←hpair]
    refine sup_le le_normalClosure ?_
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom)
      (show (P : Subgroup N) ≤ normalClosure ((P : Subgroup N) : Set N) from le_normalClosure)
    rw [show (normalClosure ((P : Subgroup N) : Set N)).map (MulAut.conj x).toMonoidHom =
      normalClosure ((P : Subgroup N) : Set N) from Normal.map_conj_eq _ _] at hh
    exact hh
  have hcore : ⁅pCore 2 N,pResidual 2 N⁆ ≤ U₀ :=
    Glauberman.core_residual_le_of_class_two_thompson_layer P U₀ hPgen hclass hPc hmove
  let Q₀ := (Q d.radical a).subgroupOf I
  let : Q₀.Normal := (normal_subgroupOf_iff_le_normalizer hQI).mpr
    (hI.trans (Q_normalized d.radical a))
  have hpQ : IsPGroup 2 Q₀ := by
    have hh : IsPGroup 2 (Q d.radical a) := hjQ ▸ pCore_isPGroup.map j
    exact hh.comap_subtype
  let L := pResidual 2 I
  have hLN : L ≤ N := by
    change pResidual 2 I ≤ N
    rw [←hres]
    exact map_subtype_le _
  have hDN : ⁅Q₀,L⁆ ≤ N := (commutator_le_right _ _).trans hLN
  have hDNcore : (⁅Q₀,L⁆.subgroupOf N) ≤ pCore 2 N :=
    le_sSup ⟨inferInstance,(hpQ.to_le (commutator_le_left _ _)).comap_subtype⟩
  have hfirst : ⁅Q₀,L⁆ ≤ (pCore 2 N).map N.subtype := by
    have hh := map_mono (f := N.subtype) hDNcore
    rwa [map_subgroupOf_eq_of_le hDN] at hh
  have hfull : ⁅Q₀,L⁆ ≤ U₁ := by
    rw [←commutator_isPPerfect_idempotent L Q₀ (isPPerfect_pResidual 2) hpQ le_normalizer_of_normal]
    have hh := map_mono (f := N.subtype) hcore
    rw [map_commutator,hres,map_subgroupOf_eq_of_le hUN] at hh
    exact (commutator_mono hfirst le_rfl).trans hh
  have hfullm : ⁅Q d.radical a,(pResidual 2 I).map I.subtype⁆ ≤ U d.radical a := by
    have hh := map_mono (f := I.subtype) hfull
    rwa [map_commutator,map_subgroupOf_eq_of_le hQI,map_subgroupOf_eq_of_le hUI] at hh
  let C := N.map I.subtype
  let e : N ≃* C := N.equivMapOfInjective I.subtype I.subtype_injective
  let : Finite C := Finite.of_surjective e e.surjective
  have hCn : (C.subgroupOf I).Normal := by
    rw [show C.subgroupOf I = N from comap_map_eq_self_of_injective I.subtype_injective N]
    infer_instance
  have hgen' : C ⊔ (pCore 2 I).map I.subtype = I := by
    have hh := congrArg (Subgroup.map I.subtype) hgen
    rwa [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  let eqQ := e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
    (IsPGroup.ker_isPGroup_of_injective (p := 2) e.symm.injective)
  have hfit' : generalizedFitting C = pCore 2 C := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hfit
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hres' : (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype := by
    rw [←map_embedded_pResidual 2 N I.subtype,hres]
  refine ⟨E,hE,I,hI,hQI,C,map_subtype_le _,hCn,hgen',⟨eqQ.trans eN⟩,hfit',hres',?_,?_,?_,?_⟩
  · refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
    change ((P : Subgroup N).map e.toMonoidHom).map C.subtype = _
    rw [Subgroup.map_map]
    exact hPB
  · rw [hres']
    exact hmoveNe
  · rw [hres']
    exact hfullm
  · rw [hres']
    exact hfullm.trans (U_le_Z a)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
