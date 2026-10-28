module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.Classical.DefiningLocalRank.LowerBounds
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.SU3.OddDefiningRank
public import Theory.Quasithin.LocalRankEmbedding

/-!
# Odd ternary rows in the nonnormal-component sieve

A centerless nonnormal component in a quasithin group has, at each odd
prime, local rank plus ordinary rank at most two. The fundamental SL₂ in
an odd PSL₃ or PSU₃ model gives positive defining-prime local rank, while
the root plane gives ordinary rank at least two. Their sum excludes both
rows of the complete Theorem C catalogue. The model equivalence and the
original Hermitian form are retained throughout.

Source: Aschbacher–Smith A.1.34(3) and A.3.8(1–2), pp.29–30 and45–46.
The actual Hall normalizer receives this additive budget from
`SourceA5HallPlacement.NonnormalCenter` without an ambient SQTK hypothesis.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.QTComponents
open Theory.SpecificGroups.DefiningLocalRank
variable {S : Type*} [Group S] [Finite S]

/-- The odd split ternary row contradicts the actual nonnormal rank budget. -/
theorem linear_three_odd_false
    (hr : ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p S + primeRank p S ≤ 2)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL S 3 p) : False := by
  obtain ⟨F, _, _, hc, ⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hc)
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hl : 1 ≤ twoLocalPrimeRank p S :=
    (psl3_fieldExponent_le_twoLocalPrimeRank hp2
      (show Nat.card F = p ^ 1 by simpa using hc)).trans
      (twoLocalPrimeRank_le_of_injective p a.symm.toMonoidHom a.symm.injective)
  have hn := PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F
    (p := p) (e := 1) (by simpa using hc)
  have hb := hr p hp ho
  rw [primeRank_equiv p a] at hb
  omega

/-- The odd unitary ternary row is excluded, including defining prime three. -/
theorem unitary_three_odd_false
    (hr : ∀ p : ℕ, p.Prime → Odd p → twoLocalPrimeRank p S + primeRank p S ≤ 2)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU S 3 p) : False := by
  obtain ⟨F, _, _, J, hc, hj, ⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective a.symm a.symm.injective
  have hl : 1 ≤ twoLocalPrimeRank p S :=
    (psu3_fieldExponent_le_twoLocalPrimeRank J ho (by decide : 0 < 1)
      (by simpa using hc) (by simpa using hj)).trans
      (twoLocalPrimeRank_le_of_injective p a.symm.toMonoidHom a.symm.injective)
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hn := HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank J
    (p := p) (e := 1) hp2 (by decide) (by simpa using hc) (by simpa using hj)
  have hb := hr p hp ho
  rw [primeRank_equiv p a] at hb
  omega

end CFSG.Quasithin.ChapterA.QTComponents
