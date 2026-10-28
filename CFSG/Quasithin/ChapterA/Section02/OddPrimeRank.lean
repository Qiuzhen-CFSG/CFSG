module

public import FeitThompson.BGsection4.lemma_4_5_a
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.GroupTheory.Schreier

/-!
# Odd-prime rank one and low-rank surjective images

For odd `p`, a noncyclic Sylow `p`-subgroup contains an elementary abelian
subgroup of order `p²`, by Bender–Glauberman Lemma 4.5(a). Its generator rank
is at least two, so prime rank at most one forces the Sylow subgroup to be
cyclic. Cyclic Sylow subgroups and vanishing prime rank pass to surjective
images. These facts give the ordinary prime-rank inequalities in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma A.2.7(1) and (3), printed p. 34.

The converse follows the proof of
`section12_sylow_cyclic_of_primeRank_le_one` in the Feit–Thompson development,
using the earlier p-group input directly to keep the import boundary narrow.
-/

public section

namespace Sylow

/-- At an odd prime, prime rank at most one forces each Sylow subgroup to be cyclic. -/
theorem isCyclic_of_primeRank_le_one_of_ne_two
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hpodd : p ≠ 2) (hrank : primeRank p G ≤ 1) :
    IsCyclic P := by
  classical
  by_contra hPcyc
  let : Fact (IsPGroup p P) := ⟨P.isPGroup'⟩
  obtain ⟨A, _, hAcard, hAelem⟩ := lemma_4_5_a hpodd hPcyc
  let : IsElementaryAbelian p A := hAelem
  have hArank : 2 ≤ Group.rank A := by
    let : CommGroup A := IsMulCommutative.instCommGroup
    have hcard_dvd : Nat.card A ∣ p ^ Group.rank A :=
      card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p A) a)
    rw [hAcard] at hcard_dvd
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hcard_dvd
  have hle : Group.rank A ≤ primeRank p P :=
    le_csSup (Theory.GroupTheory.primeRank_bdd p)
      ⟨A, IsElementaryAbelian.isPGroup p A, inferInstance, inferInstance, le_rfl⟩
  have hPG : primeRank p P ≤ primeRank p G :=
    Theory.GroupTheory.primeRank_le_of_injective p (P : Subgroup G).subtype
      (P : Subgroup G).subtype_injective
  omega

end Sylow

namespace PrimeRank

/-- Odd-prime rank cannot increase under a surjection when the source has rank at most one. -/
theorem le_of_surjective_of_source_le_one
    {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (f : G →* H) (hf : Function.Surjective f)
    (hrank : primeRank p G ≤ 1) : primeRank p H ≤ primeRank p G := by
  classical
  by_cases hzero : primeRank p G = 0
  · rw [eq_zero_of_surjective f hf hzero, hzero]
  · obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hcyclic := P.isCyclic_of_primeRank_le_one_of_ne_two hpodd hrank
    have himage := P.primeRank_le_one_of_surjective hcyclic f hf
    omega

/-- Odd-prime rank cannot increase under a surjection when the target has rank at most two. -/
theorem le_of_surjective_of_target_le_two
    {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (f : G →* H) (hf : Function.Surjective f)
    (hrank : primeRank p H ≤ 2) : primeRank p H ≤ primeRank p G := by
  by_cases hsource : primeRank p G ≤ 1
  · exact le_of_surjective_of_source_le_one hpodd f hf hsource
  · omega

end PrimeRank
