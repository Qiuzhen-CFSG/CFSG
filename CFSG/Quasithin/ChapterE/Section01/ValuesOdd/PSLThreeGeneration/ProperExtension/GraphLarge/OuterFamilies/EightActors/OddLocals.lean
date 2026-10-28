module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.OddSections
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local odd commutators for the original outer actor

An odd-prime subgroup normalized by the ambient tau need only be normal in
its join with tau. The coprime product order makes tau Sylow in that join,
and maximality identifies the literal intersection with the ambient Sylow.
The hyperplane construction and E.1.8 then produce genuine ambient rank-one
E-members with the same original actor. Their join contains its commutator
with the odd subgroup.

The concrete consumers below extract an escaping E-member if that commutator
escapes. They also allow an inner subactor in the commutator without asserting
that the subactor belongs to the original family. The normalized odd subgroup
and its noncontainment remain explicit model inputs; no uniform existence
claim, or completion of the order-eight branch, is asserted.

Source: Aschbacher--Smith E.1.8, E.1.10(6)--(8), pp.210--212, used for
E.1.14(7), p.214. The local-join argument refines the general finite-group
proof in `PSUThreeGeneration.InnerGeometry.tau_normalized_odd_commutator_le`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- Local normalization suffices for the E-generation of an odd commutator. -/
theorem normalized_odd_commutator_le_eSubgroup
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (X : Subgroup G) (hX : IsPGroup r X)
    (hn : tau (T : Subgroup G) A ≤ normalizer (X : Set G)) :
    ⁅X, A⁆ ≤ eSubgroup 1 (T : Subgroup G) A := by
  let R := tau (T : Subgroup G) A
  let H := X ⊔ R
  have hRT : R ≤ (T : Subgroup G) := tau_le _ _
  have hR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hAR : A ≤ R := le_sup_left.trans (sup_pCore_le_tau T A hAT)
  have hAH : A ≤ H := hAR.trans le_sup_right
  have hXH : X ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  let : (X.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hdisj : Disjoint X R := IsPGroup.disjoint_of_ne r 2 hr X R hX hR
  have hcard : Nat.card H = Nat.card X * Nat.card R := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes X R hn
    simpa only [hdisj.eq_bot, card_bot, one_mul] using hh.symm
  have hRcard : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv
  have hindex : (R.subgroupOf H).index = Nat.card X := by
    have hh := (R.subgroupOf H).card_mul_index
    rw [hRcard, hcard] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans (Nat.mul_comm _ _))
  have hXodd : ¬ 2 ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (((Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).mpr hr.symm).pow_right n)
  let S : Sylow 2 H := hR.comap_subtype.toSylow (by
    change ¬ 2 ∣ (R.subgroupOf H).index
    rwa [hindex])
  have hTS : T.subgroupOf H = (S : Subgroup H) :=
    S.is_maximal' T.isPGroup'.comap_subtype (by intro x hx; exact hRT hx)
  have hc := odd_normal_commutator_le_eSubgroup_one hr S
    (X.subgroupOf H) (A.subgroupOf H) hX.comap_subtype
    (by rw [← hTS]; exact comap_mono hAT)
  have hm : (eSubgroup 1 (S : Subgroup H) (A.subgroupOf H)).map H.subtype ≤
      eSubgroup 1 (T : Subgroup G) A := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro K hK
    rw [← hTS] at hK
    exact map_le_iff_le_comap.mp (le_sSup (hK.inherit T A H hAT hRH))
  have h := (map_mono (f := H.subtype) hc).trans hm
  rwa [map_commutator, map_subgroupOf_eq_of_le hXH,
    map_subgroupOf_eq_of_le hAH] at h

/-- Extract an actual ambient E-member for the original actor. -/
theorem exists_escaping_member_of_normalized_odd_commutator
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (X : Subgroup G) (hX : IsPGroup r X)
    (hn : tau (T : Subgroup G) A ≤ normalizer (X : Set G))
    (M : Subgroup G) (hmove : ¬ ⁅X, A⁆ ≤ M) :
    ∃ K : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A K ∧ ¬ K ≤ M := by
  classical
  by_contra! h
  exact hmove ((normalized_odd_commutator_le_eSubgroup T A hAT hr X hX hn).trans
    (sSup_le fun K hK => h K hK))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors

open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F]

/-- Concrete graph-extension consumer, retaining the original family member. -/
theorem familyEscapes_of_normalized_odd_commutator
    {T : Sylow 2 (graphExtension F)} {Ω : Set (Subgroup (graphExtension F))}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup (graphExtension F)))
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) (X : Subgroup (graphExtension F))
    (hX : IsPGroup r X)
    (hn : tau (T : Subgroup (graphExtension F)) A ≤ normalizer (X : Set (graphExtension F)))
    (M : Subgroup (graphExtension F)) (hmove : ¬ ⁅X, A⁆ ≤ M) :
    FamilyEscapes F T Ω M := by
  let := hΩ.1 A hA
  obtain ⟨K, hK, hKM⟩ := EightActors.exists_escaping_member_of_normalized_odd_commutator
    T A hAT hr X hX hn M hmove
  exact ⟨A, hA, hAT, K, hK, hKM⟩

/-- The inner four-group may be used inside a commutator. E-membership and
family membership continue to use the original actor A. -/
theorem familyEscapes_of_normalized_subactor_odd_commutator
    [IsSimpleGroup PSL(3,F)]
    {T : Sylow 2 (graphExtension F)} {Ω : Set (Subgroup (graphExtension F))}
    (hΩ : IsElementaryFamily Ω) {A B : Subgroup (graphExtension F)}
    (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup (graphExtension F))) (hBA : B ≤ A)
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) (X : Subgroup (graphExtension F))
    (hX : IsPGroup r X)
    (hn : (T : Subgroup (graphExtension F)) ⊓ centralizer (B : Set (graphExtension F)) ≤ normalizer (X : Set (graphExtension F)))
    (M : Subgroup (graphExtension F)) (hmove : ¬ ⁅X, B⁆ ≤ M) :
    FamilyEscapes F T Ω M := by
  have htau : tau (T : Subgroup (graphExtension F)) A ≤ (T : Subgroup (graphExtension F)) ⊓ centralizer (B : Set (graphExtension F)) := by
    intro t ht
    refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hc := (mem_centralizerModulo_iff.mp ht).2 b (hBA hb)
    rw [twoCore_eq_bot F, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  exact familyEscapes_of_normalized_odd_commutator F hΩ hA hAT hr X hX (htau.trans hn)
    M (fun h => hmove ((commutator_mono le_rfl hBA).trans h))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
