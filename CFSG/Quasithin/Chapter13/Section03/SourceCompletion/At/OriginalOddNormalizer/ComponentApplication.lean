module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.ComponentApplication
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.NormalComponent

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.ComponentApplication`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section04.NormalizedRankOneOddControl
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02 ClassificationModels
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The selected odd-normalizer component has J₄ or Rudvalis central quotient.
Residual uniqueness remains explicit here and is discharged on the original
flag by `unitary_original_terminal_component` in `TerminalComponent`. -/
theorem unitary_original_component_models (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) [IsMulCommutative A]
    (hne : A ≠ ⊥) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧
      (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
        Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
      V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) := by
  obtain ⟨K,hK,hN,hm,houtK,hcore,hmodel,hV,hR,hcent,hz,hrank⟩ :=
    unitary_original_normal_component s A hne hAN hcomm hodd hAV hu hout
  let N := normalizer (A : Set G)
  let R := oddActorResidual L A
  let J := K.map N.subtype
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  obtain ⟨_,hmove,hVcore,_⟩ := chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV
  obtain ⟨ha,_⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hcomm hodd hAV
  let a := ha.trans s.quotient
  let e : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z : (J ⧸ center J) ≃* (K ⧸ center K) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  obtain ⟨_,hdR⟩ := unitary_original_residual_embedding
    s A hAN hcomm hodd hAV K hR hz
  let j : R →* (K ⧸ center K) :=
    (QuotientGroup.mk' (center K)).comp
      ((K.equivMapOfInjective N.subtype N.subtype_injective).symm.toMonoidHom.comp
        (inclusion hR))
  have hd : 387072 ∣ Nat.card (K ⧸ center K) :=
    hdR.trans j.range.card_subgroup_dvd_card
  have hdJ : 387072 ∣ Nat.card (J ⧸ center J) := by
    rw [Nat.card_congr z.toEquiv]
    exact hd
  have h6 : 6 ≤ primeRank 2 (K ⧸ center K) := hrank
  rcases unitary_residual_theoremB_models hmodel h6 hd with hb | hrank' | hj | hru
  · exact (no_bender_of_residual_module J R V hR hVcore s.chosen.ne_bot hmove
      (hb.of_mulEquiv z)).elim
  · obtain ⟨n,hmn⟩ := hrank'
    exact (unitary_original_no_rankTwo_component R J V hR hVcore s.chosen.ne_bot
      hmove a hdJ (hmn.of_mulEquiv z)).elim
  · exact ⟨K,hK,hN,hm,houtK,hcore,Or.inl hj,hV,hR,hcent⟩
  · exact ⟨K,hK,hN,hm,houtK,hcore,Or.inr hru,hV,hR,hcent⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
