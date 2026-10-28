module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Large odd-prime ranks in proper Hall–Janko Sylow overgroups

The exhaustive full-Sylow cover puts each proper overgroup in one of the
two actual locals, of orders 1920 and 1152. Neither order contains the square
of a prime greater than three, so every such prime rank is at most one.
Sylow conjugacy preserves the original arbitrary marking.

Source: Aschbacher–Smith A.3.12(16), printed pp.47–48; the imported coverage
retains the ATLAS J2G1-p100B0 carrier and its checked word certificates.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2.SylowOvergroups
open ExceptionalParabolics

private theorem large_prime_square_not_dvd {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p ^ 2 ∣ 2 ^ 7 * 3 ^ 2 * 5 := by
  intro hd
  have hpdiv : p ∣ 2 ^ 7 * 3 ^ 2 * 5 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases hp.dvd_mul.mp hpdiv with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h
      omega
    · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three h
      omega
  · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
    subst p
    norm_num at hd

/-- Every proper full-Sylow overgroup in the actual J₂ carrier has
p-rank at most one for p > 3. -/
theorem proper_overgroup_primeRank_le_one
    (S : Sylow 2 Carrier) (D : Subgroup Carrier)
    (hSD : (S : Subgroup Carrier) ≤ D) (hD : D ≠ ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) : primeRank p D ≤ 1 := by
  let S₀ := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S S₀
  let c := MulAut.conj g
  have hS : (S : Subgroup Carrier).map c.toMonoidHom = Seed.s :=
    congrArg Sylow.toSubgroup hg
  have hDc : D.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hD
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  have hcard : Nat.card D ∣ 2 ^ 7 * 3 ^ 2 * 5 := by
    have hc : Nat.card D = Nat.card (D.map c.toMonoidHom) :=
      Nat.card_congr (c.subgroupMap D).toEquiv
    rw [hc]
    rcases proper_overgroup_le (D.map c.toMonoidHom) (hS ▸ map_mono hSD) hDc with h | h
    · exact (card_dvd_of_le h).trans (by rw [FirstParabolic.card_l₁]; norm_num)
    · exact (card_dvd_of_le h).trans (by rw [PairNormalizer.card_p₂]; norm_num)
  exact primeRank_le_one_of_square_not_dvd
    (fun hd => large_prime_square_not_dvd Fact.out hp (hd.trans hcard))

end Sporadic.LeechRelated.J2.SylowOvergroups
