module

public import Stellmacher.Recognition.MinimalSimpleOddCoreOvergroups
public import Stellmacher.Recognition.OddCoreSylow
public import GorensteinWalter.Section2.BenderSolvableUniqueness

/-!
# Fitting containment for a common Sylow overgroup

Let A be an elementary binary subgroup of order at least eight in a Sylow
two-subgroup S of an N₂ group. Every subgroup H containing S has its Fitting
subgroup inside the normalizer of the odd-core closure of A: its two-core
lies in S, and its odd core is A-invariant, so normalizes the closure by
coprime fixed-point generation and elementary commuting connectivity.

Consequently, for a minimal simple group and a maximal overgroup M of the
closure normalizer, a second maximal overgroup H containing S automatically
satisfies F(H) ≤ M. If H also contains F(M) and has nontrivial two-core,
Bender uniqueness forces H = M.

A Sylow-central involution centralizing F(M) supplies the other containment
by choosing a maximal overgroup of its centralizer. Self-centralization of
F(M) puts this involution in F(M), and even Fitting order together with the
nontrivial odd core contradicts the prime-group alternative in Bender's
theorem. Consequently its full centralizer lies in M. The hypothesis that
the involution centralizes F(M) remains explicit.

In general the common-Sylow argument supplies only one containment in a
possible Bender pair. It does not assert
that an escaping small-rank normalizer has a maximal overgroup containing S,
or that such an overgroup contains F(M) or has nontrivial two-core.

Source: GLS2, Chapter F, §19 (Bender uniqueness), §§21–22 (completed
signalizers and connectivity), and the normal prime-core Sylow containment.
-/

namespace Stellmacher.Recognition

/-- The odd core of any overgroup of the actor normalizes its closure.
The overgroup need not contain the closure or its normalizer. -/
public theorem oddCore_overgroup_le_normalizer_oddCoreClosure
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAH : A ≤ H) :
    (pPrimeCore 2 H).map H.subtype ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  apply odd_le_normalizer_oddCoreClosure_of_normalized hN A _ hA
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  · apply hAH.trans
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using (pPrimeCore 2 H).le_normalizer_map H.subtype

/-- Every overgroup of the same ambient Sylow subgroup has its Fitting
subgroup in the closure normalizer. No solvability assumption on H is needed. -/
public theorem fitting_le_normalizer_oddCoreClosure_of_common_sylow
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S) (hSH : (S : Subgroup G) ≤ H) :
    fittingSubgroupOf H ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have htwo : (pCore 2 H).map H.subtype ≤ (S : Subgroup G) := by
    rintro x ⟨y, hy, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (S.subtype hSH) hy
  have hfit : fittingSubgroup H ≤ pCore 2 H ⊔ pPrimeCore 2 H := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hq : q.val.val.Prime := Nat.prime_of_mem_primeFactors q.val.property
    let : Fact q.val.val.Prime := ⟨hq⟩
    by_cases hq2 : q.val.val = 2
    · simpa only [hq2] using (le_sup_left : pCore 2 H ≤ pCore 2 H ⊔ pPrimeCore 2 H)
    · apply le_trans ?_ le_sup_right
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := H)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)).pow_right n
  apply (Subgroup.map_mono (f := H.subtype) hfit).trans
  rw [Subgroup.map_sup]
  exact sup_le (htwo.trans (sylow_le_normalizer_oddCoreClosure hN S A hAS hA))
    (oddCore_overgroup_le_normalizer_oddCoreClosure hN A H hA (hAS.trans hSH))

/-- For maximal overgroups with a common Sylow two-subgroup, the reverse
Fitting containment in Bender uniqueness follows from the actor. -/
public theorem minimalSimple_oddCore_common_sylow_pair_eq
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (S : Sylow 2 G) (A M N : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (hR : involutionOddCoreClosure A ≠ ⊥)
    (hM : IsCoatom M) (hN : IsCoatom N)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hSN : (S : Subgroup G) ≤ N) (hcore : pCore 2 N ≠ ⊥)
    (hFMN : fittingSubgroupOf M ≤ N) : M = N := by
  have hodd : pPrimeCore 2 M ≠ ⊥ := by
    intro hbot
    have hle := (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM.lt_top hNM).1
    rw [hbot, Subgroup.map_bot] at hle
    exact hR (bot_unique hle)
  exact GorensteinWalter.maximal_eq_of_solvable_mutual_fitting_and_incompatible_cores
    hG.isSimpleGroup M N hM hN (hG.solvable_of_lt M hM.lt_top)
    (hG.solvable_of_lt N hN.lt_top) 2 hodd hcore hFMN
    ((fitting_le_normalizer_oddCoreClosure_of_common_sylow
      hG.isNTwoGroup S A N hA hAS hSN).trans hNM)

/-- A Sylow-central involution centralizing the Fitting subgroup of a maximal
closure overgroup has its full centralizer in that overgroup. Solvability
puts the involution in the Fitting subgroup. Thus Bender uniqueness applies
using the nontrivial odd core and even Fitting order of the first overgroup,
without requiring a nontrivial two-core in the second overgroup. -/
public theorem minimalSimple_oddCore_centralizer_le_of_fitting_centralizes
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (S : Sylow 2 G) (A M : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAS : A ≤ S)
    (hR : involutionOddCoreClosure A ≠ ⊥) (hM : IsCoatom M)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (t : G) (ht : orderOf t = 2) (htS : t ∈ S)
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G))
    (hFC : fittingSubgroupOf M ≤ Subgroup.centralizer ({t} : Set G)) :
    Subgroup.centralizer ({t} : Set G) ≤ M := by
  have hSM : (S : Subgroup G) ≤ M :=
    (sylow_le_normalizer_oddCoreClosure hG.isNTwoGroup S A hAS hA).trans hNM
  have hsolv := hG.solvable_of_lt M hM.lt_top
  let tm : M := ⟨t, hSM htS⟩
  have htfit : tm ∈ fittingSubgroup M := by
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hFC (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hdiv : 2 ∣ Nat.card (fittingSubgroup M) := by
    have horder : orderOf tm = 2 := (Subgroup.orderOf_coe tm).symm.trans ht
    exact horder ▸ (fittingSubgroup M).orderOf_dvd_natCard htfit
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  have hz : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    exact htne (by simpa [h] using Subgroup.mem_zpowers t)
  have hCproper : Subgroup.centralizer ({t} : Set G) < ⊤ := by
    apply lt_of_le_of_lt ?_ (hG.normalizer_lt_top (Subgroup.zpowers t) hz inferInstance)
    have hc : Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨N, hN, hCN⟩ :=
    (eq_top_or_exists_le_coatom _).resolve_left (ne_of_lt hCproper)
  have hodd : pPrimeCore 2 M ≠ ⊥ := by
    intro hbot
    have hle := (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM.lt_top hNM).1
    rw [hbot, Subgroup.map_bot] at hle
    exact hR (bot_unique hle)
  have heq : M = N := GorensteinWalter.maximal_eq_of_solvable_mutual_fitting_of_fitting_card_dvd
    hG.isSimpleGroup M N hM hN hsolv (hG.solvable_of_lt N hN.lt_top) 2 hodd hdiv
    (hFC.trans hCN)
    ((fitting_le_normalizer_oddCoreClosure_of_common_sylow
      hG.isNTwoGroup S A N hA hAS (hSC.trans hCN)).trans hNM)
  exact hCN.trans heq.ge


end Stellmacher.Recognition
