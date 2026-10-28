module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitCandidates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.GeneratorInvariance

/-!
# Held has no proper three-prime overgroups of a Sylow two-subgroup

A subgroup preserving the Held relation acts transitively on each of its
orbits, so the degree and common-neighbor profile of its induced relation are
constant. An orbit containing the seed pair is a union of seed-subgroup orbits.
A finite test on those unions forces the orbit to be exactly the pair, putting
the subgroup in the actual pair stabilizer. That stabilizer has order dividing
`2^11 * 3^2`, so its three-prime subgroups are two-groups. Sylow containment and
conjugacy then give the required overgroup equality for every Held Sylow.

The imported finite certificates prove graph preservation, the seed two-group
and orbit calculation, the finite subset test, and the pair-stabilizer order
divisibility. `overgroup_eq` assembles them without additional premises on the
fixed Held carrier. The final corollaries give the normalized three-prime
subgroup assertion inside Held and in its full permutation normalizer; only
the latter uses the bound of two on the actual normalizer quotient.

`OrbitCandidates` checks the two exceptional regular subsets and eliminates
them by their nonconstant profiles. `OrbitTest` classifies all fiber unions
of constant degree. The conditional reductions below retain their interfaces.

Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p; the missing Held-case local
application in Aschbacher–Smith, printed p.725. Candidate data and their
reproduction instructions are in `ThreePrimeOvergroups/Source/`.
-/

public section

open scoped Pointwise
open Subgroup Held.NormalizerGraph
namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

private theorem neighborCount_invariant (U : Finset (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hU : ∀ x, σ x ∈ U ↔ x ∈ U) (x : Fin 2058) :
    neighborCount U (σ x) = neighborCount U x := by
  symm
  apply Finset.card_equiv σ
  intro y
  simp only [Finset.mem_filter, hU, hσ x y]

private theorem commonCount_invariant (U : Finset (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hU : ∀ x, σ x ∈ U ↔ x ∈ U) (x y : Fin 2058) :
    commonCount U (σ x) (σ y) = commonCount U x y := by
  symm
  apply Finset.card_equiv σ
  intro z
  simp only [Finset.mem_filter, hU, hσ x z, hσ y z]

private theorem profileCount_invariant (U : Finset (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hU : ∀ x, σ x ∈ U ↔ x ∈ U) (x : Fin 2058) :
    profileCount U (σ x) = profileCount U x := by
  symm
  apply Finset.card_equiv σ
  intro y
  simp only [Finset.mem_filter, hU, commonCount_invariant U σ hσ hU]

/-- Orbit transitivity forces a three-prime subgroup containing the seed into
the actual pair stabilizer, once the finite graph test is certified. -/
theorem le_pairStabilizer_of_orbit_test
    (hgraph : permutationGroup ≤ preservingGroup)
    (hreach : ∀ x y : Fin 2058, orbitLabel x = orbitLabel y →
      ∃ g : seedSubgroup, g • x = y)
    (htest : ∀ U : Finset (Fin 2058), basepoint ∈ U →
      (∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) →
      ¬ 3 ∣ U.card →
      (∀ x ∈ U, neighborCount U x = neighborCount U basepoint) →
      (∀ x ∈ U, profileCount U x = profileCount U basepoint) → U = basePair)
    (K : Subgroup He) (hPK : seedSubgroup ≤ K) (hthree : ¬ 3 ∣ Nat.card K) :
    K ≤ pairStabilizer := by
  classical
  let U := (MulAction.orbit K basepoint).toFinset
  have hU (g : K) (x : Fin 2058) : representation g.val x ∈ U ↔ x ∈ U := by
    simp only [U, Set.mem_toFinset]
    change g • x ∈ MulAction.orbit K basepoint ↔ x ∈ MulAction.orbit K basepoint
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨g⁻¹ * k, ?_⟩
      change (g⁻¹ * k) • basepoint = x
      change k • basepoint = g • x at hk
      rw [mul_smul, hk, inv_smul_smul]
    · rintro ⟨k, rfl⟩
      exact ⟨g * k, mul_smul _ _ _⟩
  have hgraphK (g : K) : representation g.val ∈ preservingGroup :=
    hgraph g.val.property
  have hbase : basepoint ∈ U := by
    exact Set.mem_toFinset.mpr (MulAction.mem_orbit_self _)
  have hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U := by
    intro x hx y hxy
    obtain ⟨g, hg⟩ := hreach x y hxy
    let k : K := ⟨g.val, hPK g.property⟩
    have hy : representation k.val x = y := hg
    rw [← hy]
    exact (hU k x).mpr hx
  have hcard : U.card ∣ Nat.card K := by
    have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K basepoint)
    rw [Nat.card_prod, Nat.card_eq_card_toFinset] at he
    exact ⟨Nat.card (MulAction.stabilizer K basepoint), he.symm⟩
  have hregular : ∀ x ∈ U, neighborCount U x = neighborCount U basepoint := by
    intro x hx
    obtain ⟨g, rfl⟩ := Set.mem_toFinset.mp hx
    exact neighborCount_invariant U (representation g.val) (hgraphK g) (hU g) basepoint
  have hprofile : ∀ x ∈ U, profileCount U x = profileCount U basepoint := by
    intro x hx
    obtain ⟨g, rfl⟩ := Set.mem_toFinset.mp hx
    exact profileCount_invariant U (representation g.val) (hgraphK g) (hU g) basepoint
  have he := htest U hbase hsat (fun h => hthree (h.trans hcard)) hregular hprofile
  intro g hg
  change g • (basePair : Set (Fin 2058)) = (basePair : Set (Fin 2058))
  rw [← he]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  exact hU (⟨g⁻¹, K.inv_mem hg⟩ : K) x

private theorem isPGroup_of_le_pairStabilizer
    (hpair : Nat.card pairStabilizer ∣ 2 ^ 11 * 3 ^ 2)
    (K : Subgroup He) (hK : K ≤ pairStabilizer) (hthree : ¬ 3 ∣ Nat.card K) :
    IsPGroup 2 K := by
  apply IsPGroup.of_card_dvd_pow (n := 11)
  have hd : Nat.card K ∣ 2 ^ 11 * 3 ^ 2 := (card_dvd_of_le hK).trans hpair
  have hcop : (Nat.card K).Coprime (3 ^ 2) :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm).pow_right 2
  exact (hcop.dvd_mul_right).mp hd

private theorem overgroup_eq_of_seed
    (hP : IsPGroup 2 seedSubgroup)
    (hseed : ∀ K : Subgroup He, seedSubgroup ≤ K → ¬ 3 ∣ Nat.card K → IsPGroup 2 K)
    (S : Sylow 2 He) (K : Subgroup He)
    (hSK : (S : Subgroup He) ≤ K) (hthree : ¬ 3 ∣ Nat.card K) :
    K = (S : Subgroup He) := by
  obtain ⟨S₀, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He S S₀
  let e := MulAut.conj g
  let K' := K.map e.toMonoidHom
  have hSK' : (S₀ : Subgroup He) ≤ K' := by
    rw [← hg]
    exact Subgroup.map_mono hSK
  let f := K.equivMapOfInjective e.toMonoidHom e.injective
  have hc : Nat.card K = Nat.card K' := Nat.card_congr f.toEquiv
  have hpK' : IsPGroup 2 K' := hseed K' (hPS.trans hSK') (hc ▸ hthree)
  exact S.3 (hpK'.of_injective f.toMonoidHom f.injective) hSK

/-- Conditional assembly of the precise finite inputs. The seed need only be
a two-subgroup; Sylow containment and conjugacy give the assertion for every Sylow.
The concrete inputs are discharged in `overgroup_eq` below. -/
theorem overgroup_eq_of_finite_certificates
    (hgraph : permutationGroup ≤ preservingGroup)
    (hP : IsPGroup 2 seedSubgroup)
    (hreach : ∀ x y : Fin 2058, orbitLabel x = orbitLabel y →
      ∃ g : seedSubgroup, g • x = y)
    (htest : ∀ U : Finset (Fin 2058), basepoint ∈ U →
      (∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) →
      ¬ 3 ∣ U.card →
      (∀ x ∈ U, neighborCount U x = neighborCount U basepoint) →
      (∀ x ∈ U, profileCount U x = profileCount U basepoint) → U = basePair)
    (hpair : Nat.card pairStabilizer ∣ 2 ^ 11 * 3 ^ 2)
    (S : Sylow 2 He) (K : Subgroup He)
    (hSK : (S : Subgroup He) ≤ K) (hthree : ¬ 3 ∣ Nat.card K) :
    K = (S : Subgroup He) := by
  apply overgroup_eq_of_seed hP _ S K hSK hthree
  intro V hPV hVthree
  exact isPGroup_of_le_pairStabilizer hpair V
    (le_pairStabilizer_of_orbit_test hgraph hreach htest V hPV hVthree) hVthree

/-- The finite degree classification suffices after the two exceptional
common-neighbor profiles have been checked in `OrbitCandidates`. This retains
the explicit finite premises used by the unconditional assembly below. -/
theorem overgroup_eq_of_regular_candidates
    (hgraph : permutationGroup ≤ preservingGroup)
    (hP : IsPGroup 2 seedSubgroup)
    (hreach : ∀ x y : Fin 2058, orbitLabel x = orbitLabel y →
      ∃ g : seedSubgroup, g • x = y)
    (hdegrees : ∀ U : Finset (Fin 2058), basepoint ∈ U →
      (∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) →
      ¬ 3 ∣ U.card →
      (∀ x ∈ U, neighborCount U x = neighborCount U basepoint) →
      U = basePair ∨ U = candidate67 ∨ U = candidate69)
    (hpair : Nat.card pairStabilizer ∣ 2 ^ 11 * 3 ^ 2)
    (S : Sylow 2 He) (K : Subgroup He)
    (hSK : (S : Subgroup He) ≤ K) (hthree : ¬ 3 ∣ Nat.card K) :
    K = (S : Subgroup He) :=
  overgroup_eq_of_finite_certificates hgraph hP hreach
    (orbit_test_of_regular_candidates hdegrees) hpair S K hSK hthree

/-- Every three-prime overgroup of a Sylow two-subgroup of the literal Held
carrier is that Sylow subgroup. All finite calculation premises are discharged. -/
theorem overgroup_eq (S : Sylow 2 He) (K : Subgroup He)
    (hSK : (S : Subgroup He) ≤ K) (hthree : ¬ 3 ∣ Nat.card K) :
    K = (S : Subgroup He) :=
  overgroup_eq_of_regular_candidates Orbital.held_le_preservingGroup
    seedSubgroup_isPGroup seed_orbit_reachability regular_candidates
    (pairStabilizer_card_dvd Orbital.held_le_preservingGroup) S K hSK hthree

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

namespace Held.LocalPairs.SylowGeometry

/-- A three-prime subgroup of Held normalized by a Held Sylow two-subgroup
is a two-group, using the certified exclusion of proper three-prime overgroups. -/
theorem inner_normalized_three_prime_isPGroup (S : Sylow 2 He) (V : Subgroup He)
    (hnorm : (S : Subgroup He) ≤ normalizer (V : Set He))
    (hthree : ¬ 3 ∣ Nat.card V) : IsPGroup 2 V :=
  (inner_three_prime_iff_overgroups.mpr ThreePrimeOvergroups.overgroup_eq) S V hnorm hthree

/-- The three-prime subgroup clause for the full permutation normalizer.
The inner input is now proved; the sole additional assumption is the bound
on the literal quotient by the embedded Held group. -/
theorem normalized_three_prime_isPGroup
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 PermutationNormalizer) (U : Subgroup PermutationNormalizer)
    (hnorm : (T : Subgroup PermutationNormalizer) ≤ normalizer (U : Set PermutationNormalizer))
    (hthree : ¬ 3 ∣ Nat.card U) : IsPGroup 2 U :=
  normalized_three_prime_isPGroup_of_inner hbound inner_normalized_three_prime_isPGroup
    T U hnorm hthree

end Held.LocalPairs.SylowGeometry
