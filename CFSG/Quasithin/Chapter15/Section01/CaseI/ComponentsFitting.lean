module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.TwoPerfectCyclicQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
/-!
# The Case-I Fitting preimage lies in the marked local subgroup

The actual C.2.6 decomposition expresses O₂,F(G₁) using the local subgroup
and at most two outside A₃ blocks. The two-perfect residual O²(M_Z) fixes
each block, since its entire chi-block conjugacy family has at most two
members. Its action on the cyclic order-three quotient is trivial. Thus
each selected block normalizes O²(M_Z), and the source normalizer bound
puts the block in M_Z. No outside factor remains.

This proves the containment in Aschbacher--Smith 15.1.19(3), printed p.1093,
using C.2.6 directly instead of the more general intervening 15.1.19(2).
The source odd-core, radical, characteristic-control and residual-normalizer
inputs remain explicit; no selected block or component is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem twoPerfect_le_of_index_le_two (B N : Subgroup G)
    (hB : IsPPerfect 2 B) (hi : N.index ≤ 2) : B ≤ N := by
  have hpos := N.index_ne_zero_of_finite
  have hc : N.index = 1 ∨ N.index = 2 := by omega
  rcases hc with h | h
  · rw [index_eq_one.mp h]; exact le_top
  · let : N.Normal := normal_of_index_eq_two h
    have hp : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card (by
      change N.index = 2 ^ 1
      simpa only [pow_one] using h)
    have ht := hB.hom_eq_one_of_isPGroup hp ((QuotientGroup.mk' N).comp B.subtype)
    intro b hb
    exact (QuotientGroup.eq_one_iff b).mp (DFunLike.congr_fun ht ⟨b,hb⟩)

private theorem twoPerfect_normalizes_chi (X B : Subgroup G) [X.Normal]
    (hB : IsPPerfect 2 B)
    (hf : generalizedFitting X = pCore 2 X) (hr : primeRank 3 X ≤ 2)
    (K : Subgroup X) (hK : IsChiBlockIn K) :
    B ≤ normalizer (K.map X.subtype : Set G) := by
  classical
  let I := {Y : Subgroup X // IsChiBlockIn Y}
  let f : I → Subgroup G := fun i => i.val.map X.subtype
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact map_injective X.subtype_injective he
  have hsub : (Set.range fun g : G => (K.map X.subtype).map (MulAut.conj g).toMonoidHom) ⊆
      Set.range f := by
    rintro _ ⟨g,rfl⟩
    let e : X ≃* X := MulAut.conjNormal g
    refine ⟨⟨K.map e.toMonoidHom,RankOne.ChiProduct.chi_map_equiv e hK⟩,?_⟩
    change (K.map e.toMonoidHom).map X.subtype =
      (K.map X.subtype).map (MulAut.conj g).toMonoidHom
    rw [map_map,map_map]
    rfl
  have hi : (normalizer (K.map X.subtype : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans
      ((Set.ncard_range_of_injective hinj).le.trans
        (RankOne.ChiProduct.card_chiBlocks_le_two hf hr))
  exact twoPerfect_le_of_index_le_two B _ hB hi

private theorem fitting_preimage_fitting (ho : pPrimeCore 2 G = ⊥) :
    generalizedFitting (twoFittingCore G) = pCore 2 (twoFittingCore G) := by
  let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
  have he : componentLayer (twoFittingCore G) = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  rw [generalizedFitting,he,sup_bot_eq,Fitting_eq_pcore _ 2
    ((inferInstance : (twoFittingCore G).Normal).isSubnormal.pPrimeCore_eq_bot ho _)]

theorem caseI_twoFittingCore_le
    {κ : GroupClass} (hG : IsSQTK κ G) (M R : Subgroup G)
    (hr : IsPRadical 2 R) (hRM : R ≤ M)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (ho : pPrimeCore 2 G = ⊥)
    (hres : normalizer ((pResidual 2 M).map M.subtype : Set G) ≤ M) :
    twoFittingCore G ≤ M := by
  let F := twoFittingCore G
  have hfF := fitting_preimage_fitting ho
  have hf : (generalizedFitting F).map F.subtype = pCore 2 G := by
    rw [hfF,pCore_subnormal_eq_comap 2 (inferInstance : F.Normal).isSubnormal]
    exact map_comap_eq_self (by rw [range_subtype]; exact twoCore_le_twoFittingCore)
  have hcoreM : pCore 2 G ≤ M :=
    (pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le).trans hRM
  obtain ⟨n,hn,B,hB,hprod⟩ := Section02Source.fitting_ordered_product hG R M hr hcontrol hf
  have hall (i : Fin n) : B i ≤ M := by
    let Y := (pResidual 2 M).map M.subtype
    have hi := hB i
    have ha := RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hi.1).symm hi.2.2.2
    have hb : IsChiBlockIn ((B i).subgroupOf F) :=
      ⟨⟨inferInstance,ha.2.1,hi.2.2.1.subnormal.subgroupOf⟩,
        .inr ⟨3,by decide,ha⟩⟩
    have hrF : primeRank 3 F ≤ 2 :=
      (primeRank_le_of_injective 3 F.subtype F.subtype_injective).trans
        (hG.stronglyQuasithin 3 Nat.prime_three (by decide))
    have hnY := twoPerfect_normalizes_chi F Y
      (isPPerfect_embedded_pResidual 2 M) hfF hrF _ hb
    rw [map_subgroupOf_eq_of_le hi.1] at hnY
    have hcard : Nat.card (B i ⧸ pCore 2 (B i)) = 3 := by
      obtain ⟨e⟩ := hi.2.2.2.2.2.quotient_iso
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have hc : ⁅B i,Y⁆ ≤ pCore 2 G := by
      rw [commutator_comm]
      exact (commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
        (B i) Y (isPPerfect_embedded_pResidual 2 M) hnY hcard).trans
          (pCoreIn_le_of_subnormal 2 hi.2.2.1.subnormal)
    exact (normalizes_residual_of_commutator_le_two (B i) M M (pCore 2 G)
      M.le_normalizer hcoreM pCore_isPGroup le_normalizer_of_normal hc).trans hres
  have hz : n = 0 := by
    by_contra hn0
    let i : Fin n := ⟨0,Nat.pos_of_ne_zero hn0⟩
    exact (hB i).2.1 (hall i)
  subst n
  intro x hx
  obtain ⟨m,hm,l,hl,rfl⟩ := (hprod x).mp hx
  simpa using hm.1
end CFSG.Quasithin.Chapter15.Section01
