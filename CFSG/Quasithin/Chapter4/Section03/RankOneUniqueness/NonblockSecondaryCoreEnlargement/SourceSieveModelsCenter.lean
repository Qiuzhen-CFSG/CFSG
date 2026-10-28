module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsTwoCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsQuotient
public import Theory.GroupTheory.PrimeCenterRankObstruction
public import Theory.GroupTheory.PCoreInRestriction
public import GorensteinWalter.PSL2Center

/-!
This additive source variant uses only `SecondaryActionData`; it does not
assume whole-radical torus movement. The legacy conditional API is preserved.

# Excluding central covers at a cubic source torus prime

Pass to the literal ambient two-core quotient. The secondary subgroup
retains its PSL₂ quotient and positive rank at each source torus prime.
If the component center had that prime order, the center and the outside
torus actor would contribute two ranks and the secondary subgroup a third.
This contradicts the ambient SQTK bound, without assuming that the torus
centralizes the entire secondary group.

The full-quotient center catalogue has orders one and three. Thus its
center is prime to every source torus prime, and is trivial whenever
three divides the source torus order. This excludes all cubic central
covers at once, including the classical and Mathieu covers.
The remaining centerless model analysis and local normalizer inspection
remain with qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.3.18, pp.51–53; original 4.3.12(2), p.617.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The full quotient center cannot have the order of a source torus prime. -/
theorem SecondaryActionData.componentQuotient_center_card_ne_source_prime (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    Nat.card (center (s.component ⧸ pCore 2 s.component)) ≠ p := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.normal
  let N := rootNormalizer c
  let q := QuotientGroup.mk' (pCore 2 N)
  let K := SecondaryActionData.twoCoreComponent s
  let := SecondaryActionData.twoCoreComponent_normal s
  have hBN : secondary c ≤ N := s.secondary_le.trans (map_subtype_le _)
  let B₀ := (secondary c).subgroupOf N
  let B := B₀.map q
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hBk : IsPGroup 2 (q.subgroupMap B₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e₀ : B₀ ≃* secondary c := subgroupOfEquivOfLe hBN
  let e₁ := QuotientGroup.congr (pCore 2 B₀) (pCore 2 (secondary c)) e₀ (pCore_map_iso 2 e₀)
  let e₂ := (q.subgroupMap B₀).pCoreQuotientEquiv (q.subgroupMap_surjective B₀) hBk
  have hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n) :=
    s.secondary_model.of_mulEquiv (e₂.symm.trans e₁)
  have hzB : center (B ⧸ pCore 2 B) = ⊥ := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
    apply eq_bot_iff.mpr
    intro b hb
    have he : e b ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      ((centerCongr e) ⟨b, hb⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot, mem_bot] at he
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have hBr : primeRank p B = 1 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hk,
      primeRank_congr p e₀]
    exact SecondaryActionData.secondary_primeRank_eq_one s hp ho hd
  have hBK : B ≤ K := map_mono (by
    intro b hb
    exact (SecondaryActionData.secondaryToComponent s ⟨b, hb⟩).property)
  obtain ⟨a, hat, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s hp hd
  have haq : q a ∉ K := fun hi => han
    (CComponentPrimeRank.prime_actor_mem_of_twoGroup_image _ _ pCore_isPGroup ho a ha hi)
  have haqp : orderOf (q a) = p := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
    · exact fun he => haq (he ▸ K.one_mem)
  have hcomm₀ : ⁅zpowers a, B₀⁆ ≤ B₀.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 (secondary c) N hBN]
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hBN,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 (secondary c)).trans hBN)]
    rw [commutator_comm]
    exact (commutator_mono le_rfl (by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hat)).trans s.torus_secondary
  have hcomm : ⁅zpowers (q a), B⁆ ≤ B.pCoreIn 2 := by
    rw [← MonoidHom.map_zpowers, ← map_commutator,
      ← map_pCoreIn_of_ker_isPGroup q hk B₀]
    exact map_mono hcomm₀
  intro hz
  have hzK : Nat.card (center K) = p := by
    rw [Nat.card_congr (centerCongr (SecondaryActionData.twoCoreComponentEquiv s)).toEquiv]
    exact hz
  have hl := primeRank_three_of_prime_center_and_outside_actor (p := p) K B hBK hzK hzB
    (by rw [hBr]) ho (q a) haqp haq hcomm
  have hu := (SecondaryActionData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho
  omega

/-- The full component quotient has center prime to every source torus prime. -/
theorem SecondaryActionData.componentQuotient_center_coprime_of_torus_prime (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))) := by
  rcases SecondaryActionData.componentQuotient_center_card s D h with hz | hz
  · rw [hz]
    exact Nat.coprime_one_right p
  · rw [hz]
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have he : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hp.ne_one
    exact SecondaryActionData.componentQuotient_center_card_ne_source_prime s D h hp ho hd (hz.trans he.symm)

/-- A cubic source torus excludes every cubic central cover simultaneously. -/
theorem SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) : center (s.component ⧸ pCore 2 s.component) = ⊥ := by
  apply (eq_bot_iff_card _).mpr
  exact (SecondaryActionData.componentQuotient_center_card s D h).resolve_right
    (SecondaryActionData.componentQuotient_center_card_ne_source_prime s D h Nat.prime_three (by decide) hd)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
