module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Source
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import Theory.GroupTheory.GeneralizedFitting.ComponentFixedInvolution
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# Reselecting the maximal two-local at a fixed involution

Replace a maximal pushing-up witness J by (J ∩ L)S for a Sylow
two-subgroup S of J. The section-centralizer factorization and maximality
preserve its two-core and its intersection with L. A fixed core involution
then centralizes this replacement and the given ordinary component.
Choose a maximal two-local containing its full centralizer and reconstruct
the complete original witness using C.2.8.

Source: Aschbacher--Smith 4.1.3 and the reduction in 4.2.13,
printed pp.611--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem muStar_sylow_replacement {M L J : Subgroup G}
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hJ : J ∈ muStar M L (L ⊔ sectionCentralizerIn M L))
    (S : Sylow 2 J) :
    let J₀ := (J ⊓ L) ⊔ (S : Subgroup J).map J.subtype
    J₀ ≤ J ∧ J₀ ⊓ L = J ⊓ L ∧ J₀.pCoreIn 2 = J.pCoreIn 2 ∧
      J₀ ∈ muStar M L (L ⊔ sectionCentralizerIn M L) ∧ PushLE L J J₀ := by
  let C := sectionCentralizerIn M L
  let J₀ := (J ⊓ L) ⊔ (S : Subgroup J).map J.subtype
  have hJ₀J : J₀ ≤ J := sup_le inf_le_left (map_subtype_le _)
  have hsame : J₀ ⊓ L = J ⊓ L := le_antisymm (inf_le_inf_right L hJ₀J)
    (le_inf le_sup_left inf_le_right)
  have hminus : L ⊔ C ≤ M := sup_le hLM inf_le_left
  have hRJ : J.pCoreIn 2 ≤ J₀ := (pCoreIn_le_sylow J S).trans le_sup_right
  have hcores : J.pCoreIn 2 ≤ J₀.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hRJ
      (hJ₀J.trans (J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  have hne : J₀.pCoreIn 2 ≠ ⊥ := fun he => hJ.1.1.2.2.2 (bot_unique (he ▸ hcores))
  have hfactor : (J : Set G) = (J₀ : Set G) * (sectionCentralizerIn J L : Set G) := by
    apply Set.Subset.antisymm
    · intro j hj
      have hjminus : j ∈ L ⊔ C := hJ.1.1.1 hj
      have hLC : L ≤ normalizer (C : Set G) := hLM.trans (sectionCentralizerIn_normalized hML)
      change j ∈ ((L ⊔ C : Subgroup G) : Set G) at hjminus
      rw [coe_mul_of_left_le_normalizer_right L C hLC] at hjminus
      obtain ⟨l,hl,c,hc,rfl⟩ := hjminus
      obtain ⟨i,hi,q,hq,he⟩ := hJ.1.1.2.2.1 hl
      have hiL : i ∈ L := by
        have hie : i = l * q⁻¹ := by rw [←he]; simp
        rw [hie]
        exact L.mul_mem hl (L.inv_mem (pCoreIn_le 2 L hq))
      have hqcJ : q * c ∈ J := by
        have hh := J.mul_mem (J.inv_mem hi) hj
        simpa only [←he, mul_assoc, inv_mul_cancel_left] using hh
      refine ⟨i,(show J ⊓ L ≤ J₀ from le_sup_left) ⟨hi,hiL⟩,q*c,⟨hqcJ,?_⟩,?_⟩
      · exact ((C.mul_mem (componentCore_le_sectionCentralizer hLM hq) hc)).2
      · change i * (q * c) = l * c
        change i * q = l at he
        rw [←mul_assoc,he]
    · rintro _ ⟨i,hi,c,hc,rfl⟩
      exact J.mul_mem (hJ₀J hi) hc.1
  have heta : J₀ ∈ eta M L (L ⊔ C) :=
    lemma_4_1_3_1 hJ.1.1 le_rfl hJ.1.1.1 hJ₀J hne hfactor
      (fun l hl => ⟨l,(show J ⊓ L ≤ J₀ from le_sup_left) ⟨hl.2,hl.1⟩,1,one_mem _,mul_one _⟩) hminus
  have hmu : J₀ ∈ mu M L (L ⊔ C) := by
    obtain ⟨H,⟨hH,hJH⟩,hout⟩ := hJ.1.2
    exact ⟨heta,⟨H,⟨hH,hJ₀J.trans hJH⟩,hout⟩⟩
  have hpush : PushLE L J J₀ := ⟨hcores,hsame.ge⟩
  have hcore : J₀.pCoreIn 2 = J.pCoreIn 2 :=
    (eq_of_le_of_not_lt hcores (hJ.2 J₀ hmu hpush)).symm
  refine ⟨hJ₀J,hsame,hcore,⟨hmu,?_⟩,hpush⟩
  intro J₁ hJ₁ hrel hlt
  exact hJ.2 J₁ hJ₁ (hpush.trans hrel) (hcore ▸ hlt)

end CFSG.Quasithin.Chapter4

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_pushingUp_centralizer_arrangement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    ∃ (J₀ : Subgroup G) (r : H.pCoreIn 2),
      Witness L V A J₀ H W ∧ J₀ ≤ J ∧ J₀ ⊓ L = J ⊓ L ∧
      J₀.pCoreIn 2 = J.pCoreIn 2 ∧ orderOf r = 2 ∧
      K.map H.subtype ≤ centralizer ({(r : G)} : Set G) ∧
      J₀ ≤ centralizer ({(r : G)} : Set G) ∧
      ∃ H₁ : Subgroup G, IsMaximalTwoLocal H₁ ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧ J₀ ≤ H₁ ∧
        K.map H.subtype ≤ H₁ ∧ ¬ H₁ ≤ normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let I := oddActorResidual L A
  have hminus : coveringOvergroup M L I = L ⊔ C := by
    apply le_antisymm
    · exact sup_le (((oddActorResidual_le L A).trans inf_le_left).trans le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      intro l hl
      obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
      exact (coveringOvergroup M L I).mul_mem (hw.1.1.1.1 hj)
        ((show C ≤ coveringOvergroup M L I from le_sup_right)
          (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hJ : J ∈ muStar M L (L ⊔ C) := hminus ▸ hw.1
  let S : Sylow 2 J := default
  let Sg := (S : Subgroup J).map J.subtype
  let J₀ := (J ⊓ L) ⊔ Sg
  obtain ⟨hJ₀J,hsame,hcore,hstar,hpush⟩ :=
    muStar_sylow_replacement L.le_normalizer le_rfl hJ S
  have hw₀ : Witness L V A J₀ H W := by
    refine ⟨hminus.symm ▸ hstar,hw.2.1.trans hpush,hw.2.2.1,
      hJ₀J.trans hw.2.2.2.1,hw.2.2.2.2.1,?_,?_⟩
    · rw [hcore]
      exact hw.2.2.2.2.2.1
    · dsimp only
      rw [hcore]
      exact hw.2.2.2.2.2.2
  obtain ⟨r,hr,hKr,hSr⟩ := component_core_involution_fixed_by_twoSubgroup H
    hw.2.2.2.2.2.2.1.core_nontrivial K hK Sg (S.isPGroup'.map J.subtype)
    ((map_subtype_le _).trans hw.2.2.2.1)
  have hJM : J ≤ M := hJ.1.1.1.trans (sup_le L.le_normalizer inf_le_left)
  let P := L.subgroupOf J
  let : P.Normal := normal_subgroupOf_of_le_normalizer hJM
  have hPS := le_embedded_pResidual_sup_sylow_of_normalizes S P
    (show (S : Subgroup J) ≤ normalizer (P : Set J) by rw [normalizer_eq_top]; exact le_top)
  have hPmap : P.map J.subtype = L ⊓ J := subgroupOf_map_subtype L J
  have hPbound := map_mono (f := J.subtype) hPS
  rw [hPmap,Subgroup.map_sup] at hPbound
  have hres : ((pResidual 2 P).map P.subtype).map J.subtype ≤ K.map H.subtype := by
    let f : P →* (L ⊓ H : Subgroup G) := {
      toFun p := ⟨p.val.val,p.property,hw.2.2.2.1 p.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hh := map_mono (f := (L ⊓ H).subtype) (map_pResidual_le 2 f)
    rw [chosen_intersection_twoResidual_eq_solvableResidual h hw.1.1.1.2.2.1
      hw.2.2.2.1] at hh
    have he : ((pResidual 2 P).map P.subtype).map J.subtype =
        ((pResidual 2 P).map f).map (L ⊓ H).subtype := by
      rw [map_map,map_map]
      rfl
    rw [he]
    refine hh.trans ?_
    have hm := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right)] at hm
  have hJr : J₀ ≤ centralizer ({(r : G)} : Set G) := by
    apply sup_le _ hSr
    rw [inf_comm]
    exact hPbound.trans (sup_le (hres.trans hKr) hSr)
  have hrG : orderOf (r : G) = 2 := (orderOf_coe r).trans hr
  obtain ⟨H₁,hCH,hH₁⟩ := Finite.exists_le_maximal (isTwoLocal_involution_centralizer hrG)
  refine ⟨J₀,r,hw₀,hJ₀J,hsame,hcore,hr,hKr,hJr,H₁,hH₁,hCH,hJr.trans hCH,
    hKr.trans hCH,?_⟩
  intro hH₁M
  apply hout
  intro k hk
  exact ⟨k.property,hH₁M (hCH (hKr (mem_map_of_mem H.subtype hk)))⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

theorem sourceOrbit_witness_reselect_overgroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W H₁ : Subgroup G} (hw : Witness L V A J H W)
    (hH₁ : IsMaximalTwoLocal H₁) (hJH₁ : J ≤ H₁)
    (hout : ¬ H₁ ≤ normalizer (L : Set G)) :
    ∃ W₁ : Subgroup G, Witness L V A J H₁ W₁ := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  let M := normalizer (L : Set G)
  let Mminus := coveringOvergroup M L (oddActorResidual L A)
  have hsig : Mminus ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left, sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact Mminus.mul_mem (hw.1.1.1.1 hj)
      ((show sectionCentralizerIn M L ≤ Mminus from le_sup_right)
        (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hyp := source_hypothesis411 h hjoin
  have hJC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hsig.1 hw.1.1.1
  let C := sectionCentralizerIn M L
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRS' : J.pCoreIn 2 ≤ (S : Subgroup C).map C.subtype := by
    intro x hx
    exact ⟨⟨x,hJC hx⟩,hRS hx,rfl⟩
  have hc := Chapter4.Section02.Unitary.source_C28_of_muStar h D hjoin hsig hw.1 hH₁ hJH₁ hout S hRS'
  obtain ⟨c,hmark,hVW⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison h D hjoin S
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h hw.1.1.1.2.2.1 hJH₁
  have hd := chosen_oddActorResidual_counterexample_residual h D hw.1.1.1.2.2.1
    hJH₁ hw.2.2.2.2.2.1
  rw [hr] at hd
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover
    ((map_subtype_le _).trans inf_le_left) hd.1.subset
  have hsize := card_le_of_le hVW
  rw [card_map_of_injective (MulAut.conj (c : G)).injective] at hsize
  exact ⟨_,hw.1,hw.2.1,hH₁,hJH₁,
    lt_of_le_not_ge inf_le_left (fun he => hout (he.trans inf_le_right)),
    hw.2.2.2.2.2.1,hc,hd.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2,⟨e,he⟩,
    hc.oddCore_eq_bot,hc.isRadical,hc.sylow_in_normalClosure,
    hc.section_fitting_eq_core,hc.section_sylow_in_H,hsize,c,hVW⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
