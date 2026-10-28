module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalIdentification
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import GorensteinWalter.PSL2Cardinality

/-!
# A shared split prime in both Ree local quotients

A prime dividing q-1 occurs in either intrinsic parabolic-residual quotient,
PSL₂(q) or Sz(q). The actual two-coordinate torus embeds in the Ree carrier,
so that prime has ambient rank at least two. This uses no cubic divisor of
the Suzuki group. ReeLocal transports this calculation to the literal local
component used in the containing-pair contradiction.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace ReeF4.LocalPrimeRank
open Parabolics LargeLocalSeeds BenderSuzuki.MatrixGroups

/-- A prime of the split field torus has two independent coordinates in the Ree carrier. -/
theorem split_prime_rank (m : ℕ) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ 2 ^ (2 * m + 1) - 1) : 2 ≤ primeRank p (Model m) := by
  have hd' : p ∣ Nat.card (CoefficientField m)ˣ := by
    rwa [Nat.card_units,field_card]
  have hpos : 1 ≤ primeRank p (CoefficientField m)ˣ := by
    by_contra hn
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega) hd'
  have hr := Theory.GroupTheory.primeRank_le_of_injective p
    (ConverseParabolics.FullLeviRepresentation.torusHom m)
    (ConverseParabolics.FullLeviRepresentation.torusHom_injective m)
  rw [primeRank_prod_eq_add] at hr
  omega

theorem local_quotient_shared_prime {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      p ∣ Nat.card (localFactor m s ⧸ pCore 2 (localFactor m s)) ∧
      2 ≤ primeRank p (Model m) := by
  have hq : 8 ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ 2 * m + 1)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ (2 * m + 1) - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := by
    rcases hp.eq_two_or_odd with he | he
    · subst p
      have h2 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : 2 * m + 1 ≠ 0))
      have h1 := Nat.mod_eq_zero_of_dvd hd
      omega
    · exact Nat.odd_iff.mpr he
  refine ⟨p,hp,ho,?_,split_prime_rank m hd⟩
  cases s with
  | suzuki =>
    rw [Nat.card_congr (suzukiLocalQuotientEquiv m).toEquiv,suzukiMatrixGroup_card m hm]
    exact dvd_mul_of_dvd_right hd _
  | linear =>
    let e := (linearLocalQuotientEquiv m).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,field_card]
    have hf : (2 ^ (2 * m + 1)) ^ 2 - 1 =
        (2 ^ (2 * m + 1) - 1) * (2 ^ (2 * m + 1) + 1) := by
      have hsub := Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (2 * m + 1))
      have hsq := Nat.sub_add_cancel (by nlinarith : 1 ≤ (2 ^ (2 * m + 1)) ^ 2)
      nlinarith
    rw [hf]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _

end ReeF4.LocalPrimeRank
