module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Source
public import Theory.GroupTheory.CenterlessConjugatePair
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank

/-! Both original prime overcomponent rows have cubic rank at least two.
The invariant row retains it in the actual central quotient; the exchanged
row is a direct product of two copies of the original source component.
Source 2.5.19, printed pp.562–564. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem rank_three_pos_of_card {E : Type*} [Group E] [Finite E]
    (hd : 3 ∣ Nat.card E) : 1 ≤ primeRank 3 E := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  by_contra hn
  have hh := (primeRank_le_iff_elementary_card_le E (p := 3) (n := 0)).mp
    (by omega) (zpowers x) inferInstance
  rw [Nat.card_zpowers,hx,pow_zero] at hh
  omega

theorem source_prime_orbit_three_rank
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
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    2 ≤ primeRank 3 (X.map Gi.subtype) := by
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  change 2 ≤ primeRank 3 (X.map Gi.subtype)
  rw [← primeRank_equiv 3 (X.equivMapOfInjective Gi.subtype Gi.subtype_injective)]
  obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hp hp7 eK t i ht htC htZ hi
  rcases hrows with ⟨_,_,_,a,_,_,_,_,hmodel⟩ | ⟨A,hA,hm,hpair,hZA,⟨eA⟩⟩
  · have hrQ := prime_fixed_quotient_three_rank_ge_two _ hmodel
    change 2 ≤ primeRank 3 (X ⧸ center X) at hrQ
    by_contra hn
    have hsmall : primeRank 3 X ≤ 1 := by omega
    have hh := (PrimeRank.le_of_surjective_of_source_le_one (by decide : (3:ℕ)≠2)
      (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _) hsmall).trans hsmall
    omega
  · have hA3 : 1 ≤ primeRank 3 A := by
      rw [primeRank_equiv 3 eA]
      exact rank_three_pos_of_card
        (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).three_dvd_card
    change X = _ at hpair
    rw [hpair]
    exact centerless_conjugate_pair_three_rank A hZA ⟨t,htI⟩
      (commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne
        (hA.map_conj ⟨t,htI⟩) hm)) hA3
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
