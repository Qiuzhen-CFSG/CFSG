module
public import Theory.SpecificGroups.PSL3.NonsplitPrimeRank
public import Theory.SpecificGroups.PSL3.SplitPrimeActors
public import Theory.GroupAction.ComponentRankAction.ResidualSource

/-!
# Noncubic prime generation in binary ternary linear components

A component of p-rank two with p-prime center and central quotient
PSL₃(2^f) has a split torus prime: the nonsplit Sylow calculation excludes
the other primes. For p > 3 the concrete field-actor calculation then
absorbs all ambient p-elements. Both the prime-generated subgroup and the
prime-to-p residual equal the original component. Only coprimality of the
center is needed, so this includes genuine central three-covers.

Source: Aschbacher–Smith A.3.18, pp.51–53; the literal C-component
application is in NonblockEndgameSieveModelsNoncubic, for original
4.3.12(2), p.617.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.GroupAction.ComponentRankAction
noncomputable section
namespace Matrix.PSL3
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The full original component contains all ambient p-elements, for p > 3. -/
theorem binary_noncubic_component_eq_primeClosure_and_residual
    {L : Subgroup G} (hL : IsComponent G L)
    {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    L = closure {x : G | orderOf x = p} ∧ L = primeToResidual p G := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := hL.2
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    exact fun hd => (by omega : p ≠ 2)
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hpF : (p : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F hp (by omega : 2 ≠ p)
  have hrJ : 2 ≤ primeRank p PSL(3,F) := by
    rw [← primeRank_congr p e, ← primeRank_eq_of_surjective_of_coprime p
      (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective (center L))
      (by rwa [QuotientGroup.ker_mk'])]
    exact hr
  have hd : p ∣ Nat.card F - 1 := by
    by_contra hnot
    have hb := NonsplitPrimeRank.projective_rank_le_one F 2 hpq hpF hnot
    omega
  apply component_eq_primeClosure_and_residual hL hz hr hG e
  intro a ha m hm
  exact SplitPrimeActors.inner_of_primePower hf hF hp3 hd
    (action L e).range (inner_le_range L e)
    (range_rank_le_two L e hz hr hG) a ha ⟨m, hm⟩
end Matrix.PSL3
