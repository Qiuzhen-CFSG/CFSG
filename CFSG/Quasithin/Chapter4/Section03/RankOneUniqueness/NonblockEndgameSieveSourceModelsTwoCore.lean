module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsInputs
public import Theory.GroupTheory.CComponent.TwoCorePrimeActors

/-!
This additive source variant uses only `SecondarySourceData`; it does not
assume whole-radical torus movement. The legacy conditional API is preserved.

# Ordinary-component reduction for the nonblock source sieve

Quotient the root normalizer by its actual two-core. The image of K_Z is
isomorphic to its full intrinsic two-core quotient and is an ordinary normal
component. SQTK and each literal outside prime actor survive this quotient.
Thus the image cannot equal either the ambient prime-generated subgroup or
the prime-to-prime residual. For a centerless concrete model the canonical
central quotient is supplied explicitly.

The Lie-model applications use these facts to discharge the ordinary-component
hypotheses of proved A.3.18 specializations. They do not assume that O₂(K_Z)
is central, and do not identify this quotient with the source prime-to-p
quotient. Final source-model assembly remains with
qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith A.3.18, pp.51–53, and original 4.3.12(2), p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The component in the literal ambient two-core quotient of the root normalizer. -/
abbrev SecondarySourceData.twoCoreComponent (s : SecondarySourceData c n) :
    Subgroup (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)) :=
  s.component.map (QuotientGroup.mk' (pCore 2 (rootNormalizer c)))

/-- The full intrinsic quotient is identified with that actual image. -/
def SecondarySourceData.twoCoreComponentEquiv (s : SecondarySourceData c n) :
    SecondarySourceData.twoCoreComponent s ≃* s.component ⧸ pCore 2 s.component :=
  (cComponentTwoCoreQuotientEquiv s.isComponent).symm

/-- SQTK passes through the ambient two-core quotient. -/
theorem SecondarySourceData.twoCoreRoot_sqtk (_s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)) := by
  have hs := rootNormalizer_sqtk c D h
  refine ⟨?_, hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

/-- The reduced component is ordinary; no centrality of O₂(K_Z) is assumed. -/
theorem SecondarySourceData.twoCoreComponent_isComponent (s : SecondarySourceData c n) :
    IsComponent (rootNormalizer c ⧸ pCore 2 (rootNormalizer c))
      (SecondarySourceData.twoCoreComponent s) := by
  let := s.quasisimple
  exact CComponentPrimeRank.twoCore_image_isComponent s.isComponent

omit [Finite G] in
/-- The reduced component retains relative normality. -/
theorem SecondarySourceData.twoCoreComponent_normal (s : SecondarySourceData c n) :
    (SecondarySourceData.twoCoreComponent s).Normal := by
  let := s.normal
  exact (inferInstance : s.component.Normal).map _ (QuotientGroup.mk'_surjective _)

/-- A centerless model makes the reduced component center trivial. -/
theorem SecondarySourceData.twoCoreComponent_center_eq_bot (s : SecondarySourceData c n)
    {J : Type*} [Group J] (e : (s.component ⧸ pCore 2 s.component) ≃* J)
    (hz : center J = ⊥) : center (SecondarySourceData.twoCoreComponent s) = ⊥ := by
  let a := (SecondarySourceData.twoCoreComponentEquiv s).trans e
  apply eq_bot_iff.mpr
  intro x hx
  have hm : a x ∈ center J := ((centerCongr a) ⟨x, hx⟩).property
  rw [hz, mem_bot] at hm
  exact mem_bot.mpr (a.map_eq_one_iff.mp hm)

/-- The centerless full model supplies the central quotient required by
ordinary-component source theorems. -/
def SecondarySourceData.twoCoreCentralModel (s : SecondarySourceData c n)
    {J : Type*} [Group J] (e : (s.component ⧸ pCore 2 s.component) ≃* J)
    (hz : center J = ⊥) :
    (SecondarySourceData.twoCoreComponent s ⧸ center (SecondarySourceData.twoCoreComponent s)) ≃* J :=
  ((QuotientGroup.quotientMulEquivOfEq
    (SecondarySourceData.twoCoreComponent_center_eq_bot s e hz)).trans QuotientGroup.quotientBot).trans
      ((SecondarySourceData.twoCoreComponentEquiv s).trans e)

/-- The original prime torus actor remains an outside prime actor after
quotienting by the ambient two-core. -/
theorem SecondarySourceData.exists_twoCore_outside_prime_actor (s : SecondarySourceData c n)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    ∃ a : rootNormalizer c ⧸ pCore 2 (rootNormalizer c),
      orderOf a = p ∧ a ∉ SecondarySourceData.twoCoreComponent s := by
  obtain ⟨a, _, ha, han⟩ := SecondarySourceData.exists_outside_prime_actor s hp hd
  let := s.normal
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (pCore 2 (rootNormalizer c))
  have hn : q a ∉ SecondarySourceData.twoCoreComponent s := fun hi => han
    (CComponentPrimeRank.prime_actor_mem_of_twoGroup_image _ _ pCore_isPGroup ho a ha hi)
  refine ⟨q a, ?_, hn⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  · exact fun he => hn (he ▸ (SecondarySourceData.twoCoreComponent s).one_mem)

/-- Neither the prime-to-p residual nor the prime-generated closure of
the reduced ambient group can equal the reduced component. -/
theorem SecondarySourceData.twoCoreComponent_ne_prime_closures (s : SecondarySourceData c n)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    SecondarySourceData.twoCoreComponent s ≠
        closure {x : rootNormalizer c ⧸ pCore 2 (rootNormalizer c) | orderOf x = p} ∧
      SecondarySourceData.twoCoreComponent s ≠
        primeToResidual p (rootNormalizer c ⧸ pCore 2 (rootNormalizer c)) := by
  obtain ⟨a, ha, han⟩ := SecondarySourceData.exists_twoCore_outside_prime_actor s hp ho hd
  constructor
  · intro he
    exact han (he ▸ subset_closure ha)
  · intro he
    apply han
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one, ← ha] using pow_orderOf_eq_one a

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
