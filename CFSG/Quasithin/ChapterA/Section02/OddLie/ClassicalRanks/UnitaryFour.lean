module

public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks
public import Theory.NumberTheory.TwoPowerNeighbors

/-!
# The unitary dimension-four rank obstructions in A.2.17

For the actual PSU₄(r) carrier, every odd divisor s of r+1 supplies rank three
in a nonidentity involution centralizer. Local ranks at most two thus force
r+1 = 2^b, with b prime. Independent prime-field shears give ordinary defining
rank greater than two, excluding this family in the strongly quasithin case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39 (PDF p.50). No covering-group recognition or family elimination
is asserted; those earlier source premises remain with the A.2.17 assembly.
-/

public section
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02
open Theory.SpecificGroups.ClassicalUnitary.OddFourRanks
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F)
  {r : ℕ} [Fact r.Prime]

/-- The source local rank bound rules out every odd divisor of r+1. -/
theorem psu4_no_odd_prime_dvd_succ (hr : r ≠ 2) (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r)
    (hl : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ z : ProjectiveSpecialUnitaryMatrixGroup J,
      z ≠ 1 → z ^ 2 = 1 →
        primeRank s (Subgroup.centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≤ 2) :
    ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ r + 1 := by
  obtain ⟨z, hz, hz2, hge⟩ := exists_involution_three_le_primeRank J hr hc hconj
  intro s hs ho hd
  have := hge s hs ho hd
  have := hl s hs ho z hz hz2
  omega

/-- The Mersenne restriction, including r=3 and b=2. -/
theorem psu4_mersenne_parameter (hr : r ≠ 2) (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r)
    (hl : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ z : ProjectiveSpecialUnitaryMatrixGroup J,
      z ≠ 1 → z ^ 2 = 1 →
        primeRank s (Subgroup.centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≤ 2) :
    ∃ b : ℕ, b.Prime ∧ r + 1 = 2 ^ b :=
  Nat.mersenne_of_no_odd_prime_dvd_succ (Fact.out : r.Prime)
    (psu4_no_odd_prime_dvd_succ J hr hc hconj hl)

/-- Ordinary defining rank exceeds two on every allowed arbitrary-form carrier. -/
theorem psu4_defining_primeRank_gt_two (hc : Nat.card F = r ^ 2)
    (hconj : ∀ x, J.conj x = x ^ r) :
    2 < primeRank r (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (p := r) (f := 2) (by
    simpa only [← Nat.card_eq_fintype_card] using hc)
  exact lt_of_lt_of_le (by decide : 2 < 3) (Defining.three_le_primeRank J hc hconj)

end CFSG.Quasithin.ChapterA.Section02
