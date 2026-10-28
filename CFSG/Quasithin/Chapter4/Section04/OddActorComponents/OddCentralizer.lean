module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Containment
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
/-!
# The detected component has odd centralizer

Once the original V is inside K, C_N(K) lies in M and normalizes L_A.
Its intersection with L_A is a normal two-subgroup, by the actual faithful
module kernel. Component-centralizer core freeness kills that intersection,
so L_A centralizes C_N(K). Any involution in the latter would yield a
nontrivial two-subgroup normalized by L_A and centralized by K, contradicting
its genuine unique maximal-two-local overgroup.

Source: the unitary specialization of Aschbacher--Smith 4.4.10(3), printed
p.621. This proof retains the faithful-kernel hypothesis supplied by the
original natural action and does not assume component normality.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]
/-- Actual module containment and its faithful kernel force the component centralizer to be odd. -/
theorem chosen_oddNormalizer_component_centralizer_odd
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G))
    (K:Subgroup (normalizer (A:Set G))) (hK:IsComponent (normalizer (A:Set G)) K)
    (houtK:¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G))
    (hVK:V≤K.map (normalizer (A:Set G)).subtype) :
    Odd (Nat.card (centralizer (K:Set (normalizer (A:Set G))))) := by
  let N:=normalizer (A:Set G)
  let F:=oddActorResidual L A
  let J:=K.map N.subtype
  let C0:=centralizer (K:Set N)
  let C:=C0.map N.subtype
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ:C≤centralizer (J:Set G):=by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (hx y hy)
  have hCV:C≤centralizer (V:Set G):=hCJ.trans (centralizer_le hVK)
  have hCM:C≤normalizer (L:Set G):=hCV.trans ((Subgroup.centralizer_le_normalizer _).trans
    (oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).1)
  have hCN:C≤N:=map_subtype_le _
  have hCF:C≤normalizer (F:Set G):=(le_inf hCM hCN).trans (normalizes_oddActorResidual L A)
  obtain ⟨_,hFK,_⟩:=chosen_oddNormalizer_component_normalization h D A hAN hcomm hodd hAV K hK
  have hFC:F≤normalizer (C:Set G):=by
    have hh:=(map_mono (f:=N.subtype) (hFK.trans (normalizer_le_normalizer_centralizer K))).trans
      (Subgroup.le_normalizer_map N.subtype)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  have hcore:pCore 2 C0=⊥:=hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2
    (oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).2
  have hcoreC:pCore 2 C=⊥:=by
    have he:=pCore_map_iso 2 (C0.equivMapOfInjective N.subtype N.subtype_injective)
    rw [hcore,Subgroup.map_bot] at he
    exact he.symm
  have hinf:F⊓C=⊥:=by
    have hp:IsPGroup 2 (F⊓C:Subgroup G):=(isPGroup_pCoreIn 2 L).to_le
      ((inf_le_inf ((oddActorResidual_le L A).trans inf_le_left) hCV).trans hfaith)
    have hn:C≤normalizer (F⊓C:Set G):=(le_inf hCF C.le_normalizer).trans inf_normalizer_le_normalizer_inf
    have hh:=le_pCoreIn_of_normalizes hp (show F⊓C≤C from inf_le_right) hn
    rw [pCoreIn,hcoreC,Subgroup.map_bot] at hh
    exact le_bot_iff.mp hh
  have hcommFC:⁅F,C⁆=⊥:=le_bot_iff.mp ((le_inf
    (le_normalizer_iff_commutator_le_left.mp hCF)
    (le_normalizer_iff_commutator_le_right.mp hFC)).trans hinf.le)
  have hFCent:F≤centralizer (C:Set G):=commutator_eq_bot_iff_le_centralizer.mp hcommFC
  have hcOdd:Odd (Nat.card C):=by
    apply Nat.not_even_iff_odd.mp
    intro heven
    let :Fintype C:=Fintype.ofFinite C
    obtain ⟨c,hc⟩:=exists_prime_orderOf_dvd_card (G:=C) 2 (by
      simpa only [Nat.card_eq_fintype_card] using even_iff_two_dvd.mp heven)
    have hpow:(c:G)^2=1:=by
      have hh:=pow_orderOf_eq_one c
      rw [hc] at hh
      exact congrArg Subtype.val hh
    have hp:IsPGroup 2 (zpowers (c:G)):=
      (IsElementaryAbelian.zpowers_of_pow_eq_one (p:=2) hpow).isPGroup 2 _
    have hn:zpowers (c:G)≠⊥:=by
      intro hb
      have hh:(c:G)=1:=mem_bot.mp (hb ▸ mem_zpowers (c:G))
      have hh':c=1:=Subtype.ext hh
      rw [hh',orderOf_one] at hc
      omega
    have hz:zpowers (c:G)≤C:=zpowers_le.mpr c.property
    have hNZ:=normalizer_le_of_unique_maximalTwoLocal hunique.2.2 hp hn
      ((hFCent.trans (centralizer_le hz)).trans (Subgroup.centralizer_le_normalizer _))
    exact houtK (((le_centralizer_iff.mp hCJ).trans (centralizer_le hz)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNZ))
  exact (Nat.card_congr (C0.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm ▸ hcOdd
end CFSG.Quasithin.Chapter4.Section04
