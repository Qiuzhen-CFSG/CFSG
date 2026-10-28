module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Exceptional
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Kernel
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.SecondExchanged
public import Theory.GroupTheory.GeneralizedFitting.OddRankSwappedPair
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.NormalContainment
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.NoRankTwoPair
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.PairKernelNormality

/-! Normality at an involution of the actual overcomponent kernel.
The existing source census at that involution gives a normal overgroup.
Normal component dichotomy supplies containment, and the retained fixed
component rank bounds identify the original rank-two component.
This is the invariant case of source 2.5.19, printed pp.563–564. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem source_invariant_kernel_centralizer_normalizes
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (hX : let Gi := centralizer ({i} : Set G)
      IsComponent Gi (componentOrbit (K.subgroupOf Gi) (oddELayer Gi)))
    (hrX : let Gi := centralizer ({i} : Set G)
      let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
      2 ≤ primeRank 3 (X ⧸ center X))
    (j : G) (hj2 : orderOf j = 2)
    (hj : let Gi := centralizer ({i} : Set G)
      let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
      j ∈ ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi) ⊓
        centralizer (X.map Gi.subtype : Set G))) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    centralizer ({j} : Set G) ≤ normalizer (X.map Gi.subtype : Set G) := by
  let Gi := centralizer ({i} : Set G)
  let Gj := centralizer ({j} : Set G)
  let Xi := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let XA := Xi.map Gi.subtype
  have hKXi : K ≤ XA :=
    (source_overcomponent_orbit_subnormal c hG hempty hgen hb hstar
      t i ht htC htZ hi.2.1 hi.1.1 hi.1.2).2.1
  have hXj : XA ≤ Gj := fun x hx => mem_centralizer_singleton_iff.mpr (hj.2 x hx)
  have hiJ : i ∈ Gj := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hj.1.2).symm
  let ii : Gj := ⟨i,hiJ⟩
  let P := XA.subgroupOf Gj
  let Kj := K.subgroupOf Gj
  have hKj : K ≤ Gj := hKXi.trans hXj
  have hXA : IsComponentIn XA Gi := by
    refine ⟨map_subtype_le _,?_⟩
    change IsComponent Gi ((Xi.map Gi.subtype).comap Gi.subtype)
    rw [comap_map_eq_self_of_injective Gi.subtype_injective]
    exact hX
  have hPi := component_in_subgroup_centralizer XA i hXA Gj hXj hiJ
  have hjbad : BadInvolution ((S : Subgroup H).map H.subtype) K j :=
    ⟨hj.1.1,hj2,source_overcomponent_kernel_involutions c hG hempty hgen hb hstar
      t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2 j hj.2⟩
  obtain ⟨htJ,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hp hp7 eK t j ht htC htZ hjbad
  let Y := componentOrbit Kj (oddELayer Gj)
  have hYN : Y.Normal := by
    rcases hrows with ⟨_,hn,_⟩ | ⟨A,hA,hm,hpair,_⟩
    · exact hn
    · change Y = _ at hpair
      rw [hpair]
      exact exchanged_component_pair_normal (hG.involution_centralizer_sqtk hj2).stronglyQuasithin
        A hA ⟨t,htJ⟩ hm.symm
  let := hYN
  let : IsQuasisimple Xi := hX.2
  let : IsQuasisimple P := hPi.quasisimple
  let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  let : IsQuasisimple Kj := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKj).symm
  have hKjC : IsComponentIn Kj (centralizer ({(⟨t,htJ⟩ : Gj)} : Set Gj)) :=
    component_in_subgroup_centralizer K t
      (source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ) Gj hKj htJ
  have hKjP : Kj ≤ P := fun x hx => hKXi hx
  have hPY : P ≤ Y := centralizer_component_le_normal_of_common_perfect P _ Y Kj
    hPi hKjC.ne_bot hKjP (le_componentOrbit Kj (oddELayer Gj))
  let eP : P ≃* Xi := (subgroupOfEquivOfLe hXj).trans
    (Xi.equivMapOfInjective Gi.subtype Gi.subtype_injective).symm
  let : Nontrivial Xi := by
    let : IsSimpleGroup (Xi ⧸ center Xi) := IsQuasisimple.simple
    exact (QuotientGroup.mk'_surjective (center Xi)).nontrivial
  let eQ : (P ⧸ center P) ≃* (Xi ⧸ center Xi) :=
    IsQuasisimple.centralQuotientEquiv eP.toMonoidHom eP.surjective
  have hrP : 2 ≤ primeRank 3 (P ⧸ center P) := by
    rw [primeRank_equiv 3 eQ]
    exact hrX
  have hPN : P.Normal := by
    rcases hrows with ⟨hY,_,_,a,ha,hact,hB,_,hmodel⟩ |
      ⟨A,hA,hm,hpair,hZA,⟨eA⟩⟩
    · have he := rank_two_component_eq_normal_overgroup P Y ii
        ((orderOf_coe ii).symm.trans hi.2.1) hPi hY hPY hrP
        (prime_fixed_quotient_involution_component_three_rank _ hmodel)
      exact he.symm ▸ hYN
    · let : Fact p.Prime := ⟨hp.1⟩
      have hA3 : primeRank 3 A ≤ 1 := prime_threeRank_le_one hp7 (eA.trans eK)
      exact (no_rank_two_quasisimple_subgroup_of_exchanged_rank_one_pair P A hrP hA hZA hA3
        ⟨t,htJ⟩ hm.symm (hpair ▸ hPY)).elim
  exact (normal_subgroupOf_iff_le_normalizer hXj).mp hPN

/-- Every involution of the actual overcomponent kernel has a centralizer
normalizing that entire orbit. Both first rows use the original census. -/
theorem source_prime_kernel_centralizer_normalizes
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (j : G) (hj2 : orderOf j = 2)
    (hj : let Gi := centralizer ({i} : Set G)
      let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
      j ∈ ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi) ⊓
        centralizer (X.map Gi.subtype : Set G))) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    centralizer ({j} : Set G) ≤ normalizer (X.map Gi.subtype : Set G) := by
  obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hp hp7 eK t i ht htC htZ hi
  rcases hrows with ⟨hX,_,_,a,_,_,_,_,hmodel⟩ | ⟨A,hA,hm,hpair,hZA,⟨eAK⟩⟩
  · exact source_invariant_kernel_centralizer_normalizes c hG hempty hgen hb hstar
      hp hp7 eK t i ht htC htZ hi hX
      (prime_fixed_quotient_three_rank_ge_two _ hmodel) j hj2 hj
  · let Gi := centralizer ({i} : Set G)
    let Gj := centralizer ({j} : Set G)
    let ti : Gi := ⟨t,htI⟩
    let Xi := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    let XA := Xi.map Gi.subtype
    let P := A.map Gi.subtype
    change Xi = A ⊔ A.map (MulAut.conj ti).toMonoidHom at hpair
    have hPX : P ≤ XA := map_mono (hpair.symm ▸ (show A ≤ A ⊔ A.map
      (MulAut.conj ti).toMonoidHom from le_sup_left))
    have hXaJ : XA ≤ Gj := fun x hx => mem_centralizer_singleton_iff.mpr (hj.2 x hx)
    have hPj : P ≤ Gj := hPX.trans hXaJ
    have hiJ : i ∈ Gj := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hj.1.2).symm
    have hPi : IsComponentIn P Gi := by
      refine ⟨map_subtype_le _,?_⟩
      change IsComponent Gi ((A.map Gi.subtype).comap Gi.subtype)
      rw [comap_map_eq_self_of_injective Gi.subtype_injective]
      exact hA
    let eP : A ≃* P := A.equivMapOfInjective Gi.subtype Gi.subtype_injective
    have hzP : center P = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hh : eP.symm x ∈ center A := ((centerCongr eP).symm ⟨x,hx⟩).property
      rw [hZA,mem_bot] at hh
      exact eP.symm.map_eq_one_iff.mp hh
    have hcA : A ≤ centralizer (A.map (MulAut.conj ti).toMonoidHom : Set Gi) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (hA.commutator_eq_bot_of_ne (hA.map_conj ti) hm)
    have hcomm : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G) := by
      rintro x ⟨x,hx,rfl⟩ y ⟨v,⟨v,hv,rfl⟩,rfl⟩
      exact congrArg Subtype.val (hcA hx _ (mem_map_of_mem (MulAut.conj ti).toMonoidHom hv))
    have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
    have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
    have hDt := component_in_subgroup_centralizer K t hKt Gi hKi htI
    have ht2 : ti ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
    have hKnorm := NormPair.fixed_component_eq_norm hA hm.symm ht2 hDt
      (hpair ▸ le_componentOrbit (K.subgroupOf Gi) (oddELayer Gi))
    have hnorm : ∀ x ∈ P, x*(t*x*t⁻¹)∈K := by
      rintro x ⟨v,hv,rfl⟩
      have hh : componentSwapNorm hA hm.symm ⟨v,hv⟩ ∈ K.subgroupOf Gi := by
        rw [hKnorm]
        exact ⟨⟨v,hv⟩,rfl⟩
      exact hh
    have hjbad : BadInvolution ((S : Subgroup H).map H.subtype) K j :=
      ⟨hj.1.1,hj2,source_overcomponent_kernel_involutions c hG hempty hgen hb hstar
        t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2 j hj.2⟩
    have hti : Commute t i := (htZ.2 i hi.1.1).symm
    obtain ⟨htJ,hN⟩ := source_prime_pair_normal_at_kernel c hG hempty hgen hb hstar
      hp hp7 eK t i j ht htC htZ P (eP.symm.trans eAK) hzP hPi hti hiJ hPj
      hcomm hnorm hjbad
    let tj : Gj := ⟨t,htJ⟩
    let D := P.subgroupOf Gj
    let Y := D ⊔ D.map (MulAut.conj tj).toMonoidHom
    let := hN
    have hXA : XA = P ⊔ P.map (MulAut.conj t).toMonoidHom := by
      change Xi.map Gi.subtype = _
      rw [hpair,Subgroup.map_sup,map_map]
      change P ⊔ A.map ((MulAut.conj t).toMonoidHom.comp Gi.subtype) = _
      rw [←map_map]
    have hYmap : Y.map Gj.subtype = XA := by
      rw [hXA]
      change (D ⊔ D.map (MulAut.conj tj).toMonoidHom).map Gj.subtype = _
      rw [Subgroup.map_sup,map_map,map_subgroupOf_eq_of_le hPj]
      change P ⊔ D.map ((MulAut.conj t).toMonoidHom.comp Gj.subtype) = _
      rw [←map_map,map_subgroupOf_eq_of_le hPj]
    change Gj ≤ normalizer (XA : Set G)
    intro g hg
    rw [←hYmap]
    apply Y.le_normalizer_map Gj.subtype
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    rw [normalizer_eq_top Y]
    exact mem_top _
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
