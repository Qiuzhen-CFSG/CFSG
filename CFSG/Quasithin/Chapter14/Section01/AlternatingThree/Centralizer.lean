module

public import Theory.GroupTheory.CharacteristicTwoOmegaDetection
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.TwoLocalUniqueness

/-!
# The centralizer branch of the original alternating-three argument

A nontrivial normal subgroup of the characteristic-two local M meets the
original Sylow omega-center. Thus both a centerless normal N and its
nontrivial relative centralizer contain central involutions. Uniqueness of
the maximal two-local over C_G(Ω₁Z(T)) puts both factors in Mc. The Sylow
subgroup also lies in Mc. If these three factors generate M, maximality
forces M=Mc. The two involutions are distinct, giving |Ω₁Z(T)|>2.

This is the centralizer branch of Aschbacher--Smith 14.1.10, printed p.978.
No full automorphism image or Chapter 15 classification input is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
variable {G : Type*} [Group G] [Finite G]

/-- Every original nonidentity central involution has its centralizer in Mc. -/
theorem central_involution_centralizer_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ≤ Mc := by
  have hz2 := ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.1
  have hl := isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hne)
  obtain ⟨H, hCH, hH⟩ := Finite.exists_le_maximal hl
  have hZH : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ H :=
    (centralizer_le (Set.singleton_subset_iff.mpr hz)).trans hCH
  have he : H = Mc := Set.mem_singleton_iff.mp (hu ▸ ⟨hH,hZH⟩)
  exact he ▸ hCH

omit [Finite G] in
/-- The unique local over the full omega-centralizer also contains the original Sylow. -/
theorem sylow_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc}) :
    (T : Subgroup G) ≤ Mc := by
  have hm : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  apply le_trans _ hm.2
  intro t ht z hz
  exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm

/-- A nontrivial relative centralizer proves the full conclusion of 14.1.10. -/
theorem conclusion_of_nontrivial_centralizer
    (T : Sylow 2 G) {M Mc N : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (hNM : N ≤ M) (hn : (N.subgroupOf M).Normal) (hne : N ≠ ⊥)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hz : center N = ⊥)
    (hK : M ⊓ centralizer (N : Set G) ≠ ⊥)
    (hgen : (N ⊔ (M ⊓ centralizer (N : Set G))) ⊔ (T : Subgroup G) = M) :
    M = Mc ∧ 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
  classical
  let K := M ⊓ centralizer (N : Set G)
  have hMN := (normal_subgroupOf_iff_le_normalizer hNM).mp hn
  have hKn : (K.subgroupOf M).Normal := by
    have he : K.subgroupOf M = (centralizer (N : Set G)).subgroupOf M := by
      ext x
      simp only [K,mem_subgroupOf,mem_inf,x.property,true_and]
    rw [he]
    exact normal_subgroupOf_of_le_normalizer
      (hMN.trans (normalizer_le_normalizer_centralizer N))
  obtain ⟨z,hzN,hzZ,hz1⟩ := exists_omegaCenter_mem_normal M N T hM.2 hNM hn hc hne
  obtain ⟨w,hwK,hwZ,hw1⟩ := exists_omegaCenter_mem_normal M K T hM.2 inf_le_left hKn hc hK
  have hKMc : K ≤ Mc := by
    apply le_trans _ (central_involution_centralizer_le_partner T hu hzZ hz1)
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hk.2 z hzN).symm)
  have hNMc : N ≤ Mc := by
    apply le_trans _ (central_involution_centralizer_le_partner T hu hwZ hw1)
    intro n hnN
    exact mem_centralizer_singleton_iff.mpr (hwK.2 n hnN)
  have hMMc : M ≤ Mc := by
    rw [←hgen]
    exact sup_le (sup_le hNMc hKMc) (sylow_le_partner T hu)
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  refine ⟨le_antisymm hMMc (hM.1.2 hMc.1 hMMc), ?_⟩
  have hzw : z ≠ w := by
    intro he
    have hzK : z ∈ K := he ▸ hwK
    have hzC : (⟨z,hzN⟩ : N) ∈ center N :=
      mem_center_iff.mpr (fun n => Subtype.ext (hzK.2 n n.property))
    rw [hz,mem_bot] at hzC
    exact hz1 (congrArg Subtype.val hzC)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let f : Fin 3 → Z := ![1,⟨z,hzZ⟩,⟨w,hwZ⟩]
  have hf : Function.Injective f := by
    intro a b he
    fin_cases a <;> fin_cases b <;>
      simp_all [f,Subtype.ext_iff]
  have hh := Nat.card_le_card_of_injective f hf
  norm_num only [Nat.card_fin] at hh
  change 3 ≤ Nat.card (omegaOneCenterAmbient (T : Subgroup G)) at hh
  omega

end CFSG.Quasithin.Chapter14.AlternatingThree
