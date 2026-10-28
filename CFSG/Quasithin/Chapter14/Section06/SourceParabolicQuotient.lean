module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuotientRank
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.ElementaryImages

/-!
# The actual normal elementary image in original 14.6.10(4)

The original conjugate span U_H is elementary and normal in H. Since it
centralizes u, it lies in T∩I and hence in the second parabolic. Original
14.6.8 then gives its literal O₃′ quotient image rank at least four if
F*(I) differs from O₂(I). The involution supplied by 1.1.5 cannot lie in
O₂(I), because a component fails to centralize it. It therefore survives
centrally in the same quotient parabolic and determines its orientation.

Source: Aschbacher--Smith, 14.6.7--8 and 14.6.10(4), printed pp.1024--1028.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF
variable {G : Type*} [Group G] [Finite G]

open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The original U_H gives the normal elementary subgroup required by
14.6.10(4) in the literal prime-to-three quotient. -/
theorem source_parabolic_quotient_elementary_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (I2 : Subgroup G) (hSI2 : (T : Subgroup G) ⊓ I ≤ I2)
    (hI2H : I2 ≤ H) (A : Subgroup I)
    (htriple : ChapterF.IsGoldschmidtTriple A (I2.subgroupOf I))
    (hF : generalizedFitting I ≠ pCore 2 I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
    let B := I2.subgroupOf I
    U.map q ≤ B.map q ∧ IsElementaryAbelian 2 (U.map q) ∧
      ((U.map q).subgroupOf (B.map q)).Normal ∧
      4 ≤ primeRank 2 (U.map q) := by
  classical
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have hUT : D.UH ≤ (T : Subgroup G) := h.UH_le_QH.trans h.QH_le_T
  have hUI : D.UH ≤ I := by
    intro v hv
    apply hI.1.2.1
    refine ⟨hUT hv,?_⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg D.UH.subtype (mul_comm (⟨v,hv⟩ : D.UH) ⟨u,hu⟩))
  have hUI2 : D.UH ≤ I2 := (le_inf hUT hUI).trans hSI2
  let U := D.UH.subgroupOf I
  let B := I2.subgroupOf I
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUI
  let : IsElementaryAbelian 2 (U.map q) := IsElementaryAbelian.map q
  have hUB : U ≤ B := comap_mono hUI2
  have hN : (U.subgroupOf B).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [←subgroupOf_normalizer_eq hUI]
    exact comap_mono (hI2H.trans (le_normalizer_conjugateSpanBy _ _))
  refine ⟨map_mono hUB,show IsElementaryAbelian 2 (U.map q) from inferInstance,
    goldschmidt_elementary_quotient_normal U hUB hN,?_⟩
  have hbound := (source_lemma_14_6_8 hG T hempty hM hunique hmany hcard e
    hab H hH u hu I hI S hS hF).2
  have hfour : 4 ≤ Nat.log 2 ((I.pCoreIn 2).relIndex D.UH) := hrank.trans hbound
  have hcore : (I.pCoreIn 2).subgroupOf I = pCore 2 I :=
    comap_map_eq_self_of_injective I.subtype_injective _
  rw [←relIndex_subgroupOf hUI,hcore] at hfour
  exact hfour.trans (goldschmidt_elementary_quotient_rank htriple U hUB)

/-- The central involution from original 1.1.5 survives the prime-to-three
quotient and remains central in the actual second parabolic. -/
theorem source_parabolic_quotient_center_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (I2 : Subgroup G) (hSI2 : (T : Subgroup G) ⊓ I ≤ I2)
    (hI2H : I2 ≤ H) (A : Subgroup I)
    (htriple : ChapterF.IsGoldschmidtTriple A (I2.subgroupOf I))
    (hF : generalizedFitting I ≠ pCore 2 I)
 :
    Subgroup.center ((I2.subgroupOf I).map
      (QuotientGroup.mk' (pPrimeCore 3 I))) ≠ ⊥ := by
  classical
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  obtain ⟨⟨z,hz,h115⟩,_,hodd⟩ :=
    source_lemma_14_6_7_initial hG T hempty hM hunique hmany hcard e hab H hH
      u hu I hI.1 S hS
  have hzS : z ∈ (T : Subgroup G) ⊓ I := hS ▸ h115.mem_sylow
  let zi : I := ⟨z,hzS.2⟩
  let B := I2.subgroupOf I
  have hzB : zi ∈ B := hSI2 hzS
  have hzN : zi ∉ pCore 2 I := by
    intro hzi
    have hcomp : ∃ K : Subgroup I, IsComponent I K := by
      by_contra hnone
      have hE : componentLayer I = ⊥ := by
        apply le_bot_iff.mp
        exact sSup_le fun K hK => (hnone ⟨K,hK⟩).elim
      apply hF
      rw [generalizedFitting,hE,sup_bot_eq,Fitting_eq_pcore I 2 hodd]
    obtain ⟨K,hK⟩ := hcomp
    let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
    have hcentral := hK.le_centralizer_of_solvable_normal (pCore 2 I)
    apply (h115.component_inputs K hK).1
    intro k hk
    obtain ⟨a,ha,rfl⟩ := hk
    apply h115.centralizer_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact congrArg I.subtype (hcentral ha zi hzi)
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  have hzq : q zi ≠ 1 := by
    intro he
    apply hzN
    rw [←htriple.right_inf_primeToThreeCore]
    exact ⟨hzB,(QuotientGroup.eq_one_iff zi).mp he⟩
  let zb : B.map q := ⟨q zi,mem_map_of_mem q hzB⟩
  have hzb : zb ∈ Subgroup.center (B.map q) := by
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    obtain ⟨a,ha,he⟩ := b.property
    change (b : I ⧸ pPrimeCore 3 I) * q zi = q zi * b
    rw [←he,←map_mul,←map_mul]
    apply congrArg q
    apply Subtype.ext
    exact (h.H_centralizes (hI2H ha) z hz).symm
  intro hc
  have he : zb = 1 := mem_bot.mp (hc ▸ hzb)
  exact hzq (congrArg Subtype.val he)

end CFSG.Quasithin.Chapter14.Section06
