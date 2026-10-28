module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Reduction
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.StarRankReduction
public import GorensteinWalter.PSL2Cardinality

/-!
# The constrained enlargement when the original quotient has primes three and five

The odd-prime rank bounds for the selected component give cubic rank at most
one. Every odd prime of the original quotient survives in its containing
component's two-core quotient. The actual C.2.7 comparison therefore forces
binary SL₂, which contradicts strict local enlargement with the full Sylow.

This uses divisibility by both three and five explicitly; it does not assume
that a non-A₅ quotient has either prime. The remaining quotient branches and
containing-pair distinctness stay with the half-Sylow uniqueness owner.
Source: Aschbacher--Smith, 10.2.6, printed pp.748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H K : Subgroup G} {s : G}

namespace RankedEnlargement
variable (E : RankedEnlargement D H s K)
include E

/-- Inclusion and removal of a two-core preserve all the original odd primes. -/
theorem odd_primes_retained {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    p ∣ Nat.card (K ⧸ pCore 2 K) := by
  have hpos : 0 < primeRank p (L ⧸ pCore 2 L) :=
    Nat.pos_of_ne_zero (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hp)
  rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup] at hpos
  have hLK : primeRank p L ≤ primeRank p K := by
    rw [primeRank_congr p ((MulAut.conj s).subgroupMap L)]
    exact primeRank_mono p E.strict.le
  by_contra hd
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup] at hz
  omega

/-- The C.2.7 branch is impossible if the original quotient retains three and five. -/
theorem not_constrained_of_three_five
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L)) :
    generalizedFitting K ≠ pCore 2 K := by
  intro hf
  obtain ⟨F,⟨e⟩⟩ := source_rank_one_coreQuotient_linearTwo (E.c27_input hf)
    (E.ranks 3 (by decide) (by decide) h3) (E.odd_primes_retained (by decide) h5)
  exact E.not_binary_rank_one e


omit E in
private theorem binary_even_primes {n : ℕ} (he : Even n) :
    3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧ 5 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hpos : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
  have hthree : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num [Nat.pow_mod]
  have hfive : (2 ^ n) ^ 2 % 5 = 1 := by
    obtain ⟨k,rfl⟩ := he
    rw [← pow_mul, show (k + k) * 2 = 4 * k by omega, pow_mul]
    norm_num [Nat.pow_mod]
  have hsub := Nat.sub_add_cancel hpos
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have h5 : 5 ∣ (2 ^ n) ^ 2 - 1 := by omega
  exact ⟨dvd_mul_of_dvd_right h3 _,dvd_mul_of_dvd_right h5 _⟩

/-- The even-degree binary rank-one source row supplies both relevant primes;
no A₅ quotient identification is needed. -/
theorem not_constrained_of_even_binary_quotient {n : ℕ} (_hn : 2 ≤ n) (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    generalizedFitting K ≠ pCore 2 K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  have hc : Nat.card (L ⧸ pCore 2 L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  obtain ⟨h3,h5⟩ := binary_even_primes he
  exact E.not_constrained_of_three_five (hc.symm ▸ h3) (hc.symm ▸ h5)

end RankedEnlargement

/-- Apply the constrained contradiction to the actual strict factor in the pair. -/
theorem ContainingPair.exists_nonconstrained_of_three_five
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂)
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L)) :
    ∃ (s : G) (K : Subgroup G), RankedEnlargement D H s K ∧
      generalizedFitting K ≠ pCore 2 K := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact ⟨s,K,E,E.not_constrained_of_three_five h3 h5⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
