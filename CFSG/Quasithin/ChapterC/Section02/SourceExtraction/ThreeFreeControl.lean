module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.SylowCommutingJoin
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.PPrimeCore

/-!
# Three-free normal subgroups under characteristic-normalizer control

In a characteristic-two SQTK group, a normal three-free subgroup whose
Sylow intersection lies in R is contained in the control subgroup M.
The actual join with R inherits characteristic two. Its ordered C.1.29
product has no factors, since every chi-zero block contains a cubic.

If M is a {2,3}-group containing an ambient Sylow two-subgroup and its
two-core lies in R, its intersection with O₃′(G) is a normal two-subgroup.
This supplies that Sylow intersection without an extra containment premise.

Source: Aschbacher–Smith C.2.5 and its application in 14.7.26,
printed pp.145 and1053, refs/quasithin.pdf. The original application is
LocalReduction.ExtraspecialFourCharacteristic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic-normalizer control absorbs a normal three-free subgroup
whose Sylow intersection lies in the original two-group. -/
theorem normal_three_free_le_control
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (R M N : Subgroup G) [N.Normal]
    (hR : IsPGroup 2 R) (hcore : pCore 2 G ≤ R)
    (hcpu : R.characteristicNormalizerClosure ≤ M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hthree : ¬ 3 ∣ Nat.card N)
    (S : Sylow 2 N) (hS : (S : Subgroup N).map N.subtype ≤ R) : N ≤ M := by
  let J := N ⊔ R
  obtain ⟨T,hT⟩ := exists_sylow_join_eq_intersection N R R hR le_rfl
    (by rw [N.normalizer_eq_top]; exact le_top) S hS
  have hf : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le J hc (hcore.trans le_sup_right))
  have hctl : (T : Subgroup J).characteristicNormalizerClosure ≤ M.subgroupOf J := by
    rw [hT]
    exact characteristicNormalizerClosure_subgroupOf_le le_sup_right hcpu
  obtain ⟨n,_,B,hB,_,_,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
      (hG.subgroup J) hf T (M.subgroupOf J) hctl
  have h3R : ¬ 3 ∣ Nat.card R := by
    obtain ⟨a,ha⟩ := hR.exists_card_eq
    rw [ha]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have h3J : ¬ 3 ∣ Nat.card J := by
    intro hd
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes N R
      (by rw [N.normalizer_eq_top]; exact le_top)
    have hdprod : 3 ∣ Nat.card N * Nat.card R := by
      rw [hprod]
      exact dvd_mul_of_dvd_right hd _
    exact (Nat.prime_three.dvd_mul.mp hdprod).elim hthree h3R
  have hn : n = 0 := by
    by_contra hn
    let i : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
    exact h3J ((RankOne.ChiProduct.three_dvd_card_of_chi (hB i).2.chi).trans
      (card_subgroup_dvd_card (B i)))
  subst n
  intro a ha
  obtain ⟨m,b,he⟩ := hprod ⟨a,mem_sup_left ha⟩
  simp only [List.ofFn_zero,List.prod_nil,mul_one] at he
  have hm : (m : J) ∈ M.subgroupOf J := m.property
  rw [←he] at hm
  exact hm

/-- In the original characteristic-two setup, a {2,3} Sylow overgroup
absorbs the prime-to-three core. -/
theorem primeToThreeCore_le_control
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (R M : Subgroup G) (hR : IsPGroup 2 R) (hcore : pCore 2 G ≤ R)
    (hcpu : R.characteristicNormalizerClosure ≤ M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hM : IsPiGroup twoThreePrimes M) (hRM : M.pCoreIn 2 ≤ R)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) : pPrimeCore 3 G ≤ M := by
  let N := pPrimeCore 3 G
  have hthree : ¬ 3 ∣ Nat.card N :=
    Nat.prime_three.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal N (inferInstance : N.Normal).isSubnormal
  have hNM : N ⊓ M ≤ M.pCoreIn 2 := by
    have hp : IsPGroup 2 (N.subgroupOf M) := isPGroup_two_of_isPiGroup_twoThree
      (hM.of_injective (N.subgroupOf M).subtype (N.subgroupOf M).subtype_injective)
      (fun hd => hthree (hd.trans (card_comap_dvd_of_injective N M.subtype M.subtype_injective)))
    have hle : N.subgroupOf M ≤ pCore 2 M := le_sSup ⟨inferInstance,hp⟩
    have hm := map_mono (f := M.subtype) hle
    rwa [subgroupOf_map_subtype] at hm
  apply normal_three_free_le_control hG R M N hR hcore hcpu hc hthree S
  rintro _ ⟨s,hs,rfl⟩
  apply hRM
  apply hNM
  refine ⟨s.property,hTM ?_⟩
  change s ∈ (T : Subgroup G).subgroupOf N
  rwa [←hS]
end CFSG.Quasithin.ChapterC.Section02Source
