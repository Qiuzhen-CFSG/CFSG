module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.PairExclusion
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.SecondExchanged
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.NormalContainment
public import Theory.GroupTheory.GeneralizedFitting.OddRankSwappedPair
public import Theory.GroupTheory.CenterlessConjugatePair

/-! The original bad-involution census already gives the normal containing
row at a kernel involution. The norm words force containment of the first
factor. The invariant row has no two commuting prime factors; in the
exchanged row the pair has the same order, hence is the whole normal row.
This closes the pair case of source 2.5.19, printed pp.563–564. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_prime_pair_normal_at_kernel
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i j : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (P : Subgroup G) (ePK : P ≃* K) (hzP : center P = ⊥)
    (hPi : IsComponentIn P (centralizer ({i} : Set G)))
    (hti : Commute t i)
    (hiJ : i ∈ centralizer ({j} : Set G))
    (hPj : P ≤ centralizer ({j} : Set G))
    (hcomm : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G))
    (hnorm : ∀ x ∈ P, x * (t*x*t⁻¹) ∈ K)
    (hj : BadInvolution ((S : Subgroup H).map H.subtype) K j) :
    ∃ htJ : t ∈ centralizer ({j} : Set G),
      let Gj := centralizer ({j} : Set G)
      let D := P.subgroupOf Gj
      (D ⊔ D.map (MulAut.conj (⟨t,htJ⟩ : Gj)).toMonoidHom).Normal := by
  classical
  obtain ⟨htJ,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar hp hp7 eK
    t j ht htC htZ hj
  refine ⟨htJ,?_⟩
  let Gj := centralizer ({j} : Set G)
  let D := P.subgroupOf Gj
  let tt : Gj := ⟨t,htJ⟩
  let ii : Gj := ⟨i,hiJ⟩
  let Kj := K.subgroupOf Gj
  let Y := componentOrbit Kj (oddELayer Gj)
  let X := D ⊔ D.map (MulAut.conj tt).toMonoidHom
  have hYN : Y.Normal := by
    rcases hrows with ⟨_,hn,_⟩ | ⟨A,hA,hm,hpair,_⟩
    · exact hn
    · change Y = _ at hpair
      rw [hpair]
      exact exchanged_component_pair_normal
        (hG.involution_centralizer_sqtk hj.2.1).stronglyQuasithin A hA tt hm.symm
  let := hYN
  have hD := component_in_subgroup_centralizer P i hPi Gj hPj hiJ
  have hDcomm : D ≤ centralizer (D.map (MulAut.conj tt).toMonoidHom : Set Gj) := by
    intro x hx y hy
    obtain ⟨v,hv,rfl⟩ := hy
    exact Subtype.ext (hcomm hx _ (mem_map_of_mem (MulAut.conj t).toMonoidHom hv))
  have hDY : D ≤ Y := centralizer_component_le_normal_of_norm_words D _ Y hD tt
    (mem_centralizer_singleton_iff.mpr (Subtype.ext hti.eq)) hDcomm (by
      intro x hx
      exact (le_componentOrbit Kj (oddELayer Gj)) (hnorm x hx))
  have hXY : X ≤ Y := sup_le hDY (by
    rintro x ⟨y,hy,rfl⟩
    exact (inferInstance : Y.Normal).conj_mem y (hDY hy) tt)
  rcases hrows with ⟨hY,_,_,a,ha,hact,hB,_,hmodel⟩ |
    ⟨A,hA,hm,hpair,hZA,⟨eA⟩⟩
  · let eD : PSL(2,ZMod p) ≃* D := eK.symm.trans
      (ePK.symm.trans (subgroupOfEquivOfLe hPj).symm)
    let f : PSL(2,ZMod p) →* Y := (inclusion hDY).comp eD.toMonoidHom
    let n : normalizer (Y : Set Gj) := ⟨tt,le_normalizer_of_normal (mem_top tt)⟩
    let b := Y.normalizerMonoidHom n
    let g : PSL(2,ZMod p) →* Y := b.toMonoidHom.comp f
    have hf : Function.Injective f := (inclusion_injective hDY).comp eD.injective
    have hg : Function.Injective g := b.injective.comp hf
    exact (prime_fixed_quotient_no_commuting_prime_pair _ hmodel hp.1 hp7 f g hf hg (by
      intro x y
      apply Subtype.ext
      exact (hDcomm (eD x).property _
        (mem_map_of_mem (MulAut.conj tt).toMonoidHom (eD y).property)).symm)).elim
  · have hzD : center D = ⊥ := by
      apply eq_bot_iff.mpr
      intro d hd
      have hh : (subgroupOfEquivOfLe hPj) d ∈ center P :=
        (centerCongr (subgroupOfEquivOfLe hPj) ⟨d,hd⟩).property
      rw [hzP,mem_bot] at hh
      exact (subgroupOfEquivOfLe hPj).map_eq_one_iff.mp hh
    have hAc : A ≤ centralizer (A.map (MulAut.conj tt).toMonoidHom : Set Gj) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (hA.commutator_eq_bot_of_ne (hA.map_conj tt) hm)
    change Y = A ⊔ A.map (MulAut.conj tt).toMonoidHom at hpair
    have hcard : Nat.card Y = Nat.card X := by
      change Nat.card Y = Nat.card (D ⊔ D.map (MulAut.conj tt).toMonoidHom : Subgroup Gj)
      rw [hpair,centerless_conjugate_pair_card A hZA tt hAc,
        centerless_conjugate_pair_card D hzD tt hDcomm,
        Nat.card_congr ((subgroupOfEquivOfLe hPj).trans ePK).toEquiv,
        Nat.card_congr eA.toEquiv]
    have he : X = Y := eq_of_le_of_card_ge hXY hcard.le
    change X.Normal
    rw [he]
    exact hYN
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
