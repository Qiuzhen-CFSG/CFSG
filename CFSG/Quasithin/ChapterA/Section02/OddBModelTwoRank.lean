module
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.Classical.DefiningLocalRank.FourCentralizer
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.OddG2TwoRank
public import Theory.SpecificGroups.OddFourProjectiveRank

/-!
# Two-rank bounds for odd Theorem B models

The degree-two and degree-three rows have two-rank at most two. For G₂ the
faithful octonion action and its fixed unit give the sufficient bound seven.
The degree-four projective rows have bound six by their determinant-one
representations and actual central cyclic kernels. Thus all seven odd rows
are excluded from a component central quotient of two-rank at least eight.

Source: Aschbacher–Smith, Theorem B and 4.4.3, printed pp.4 and622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02
open ClassificationModels
variable {S : Type*} [Group S] [Finite S]

/-- The field witness of an odd PSL₂ model gives its dihedral two-rank bound. -/
theorem odd_psl_two_twoRank_le_two {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSL S 2 q) : primeRank 2 S ≤ 2 := by
  obtain ⟨F, hF, hfinite, hc, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, k, hp, hk, hq⟩ := (isPrimePow_nat_iff (Nat.card F)).mp (by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.isPrimePow_card F)
  have hp2 : p ≠ 2 := by
    intro he
    have hqeven : Even q := by
      rw [← hc, ← hq, he]
      exact even_two.pow_of_ne_zero (by omega)
    exact (Nat.not_even_iff_odd.mpr ho) hqeven
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, k, hp, hp.odd_of_ne_two hp2, by omega, hq.symm⟩
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  rw [primeRank_equiv 2 e]
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 Matrix.ProjectiveSpecialLinearGroup.toPGL
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
    (Theory.PSL2.odd_pgl_two_rank F hodd)

/-- All odd-field degree-three linear rows, including square fields. -/
theorem odd_psl_three_twoRank_le_two {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSL S 3 q) : primeRank 2 S ≤ 2 := by
  obtain ⟨F, hF, hfinite, hc, ⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.DefiningLocalRank.psl3_two_rank_le
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hc))

/-- The fixed-field convention is retained for every odd unitary parameter. -/
theorem odd_psu_three_twoRank_le_two {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSU S 3 q) : primeRank 2 S ≤ 2 := by
  obtain ⟨F, hF, hfinite, J, hc, _hconj, ⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv S e.toEquiv
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.DefiningLocalRank.psu3_two_rank_le J
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hc)

/-- The full octonion model has rank strictly below the source rank-eight bound. -/
theorem odd_g2_twoRank_le_seven {q : ℕ} (ho : Odd q)
    (hm : IsG2At S q) : primeRank 2 S ≤ 7 := by
  obtain ⟨F, hF, hfinite, hc, ⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Atlas.G2.odd_twoRank_le_seven
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hc))

/-- Rank eight reduces the exact odd Theorem B list to its degree-four rows. -/
theorem IsTheoremBOddModel.four_dimensional_of_twoRank_ge_eight
    (hm : IsTheoremBOddModel S) (hr : 8 ≤ primeRank 2 S) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp S 2 p) ∨
    (∃ r : ℕ, r.Prime ∧ (∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) ∧
      ClassicalGroup.IsPSL S 4 r) ∨
    (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧
      ClassicalGroup.IsPSU S 4 s) := by
  cases hm with
  | linear_two q ho h => have := odd_psl_two_twoRank_le_two ho h; omega
  | linear_three p k _ ho _ h =>
      have := odd_psl_three_twoRank_le_two (ho.pow) h; omega
  | unitary_three p k _ ho _ h =>
      have := odd_psu_three_twoRank_le_two (ho.pow) h; omega
  | symplectic p hp ho h => exact Or.inl ⟨p, hp, ho, h⟩
  | g2 p _ ho h => have := odd_g2_twoRank_le_seven ho h; omega
  | linear_four r hp hf h => exact Or.inr (Or.inl ⟨r, hp, hf, h⟩)
  | unitary_four s hp hm h => exact Or.inr (Or.inr ⟨s, hp, hm, h⟩)
/-- Every odd linear four-space central quotient has two-rank at most six. -/
theorem odd_psl_four_twoRank_le_six {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSL S 4 q) : primeRank 2 S ≤ 6 := by
  obtain ⟨F, hF, hfinite, hc, ⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.OddFourProjectiveRank.psl_four_twoRank_le_six
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hc))

/-- Every odd unitary four-space projective image has two-rank at most six. -/
theorem odd_psu_four_twoRank_le_six {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSU S 4 q) : primeRank 2 S ≤ 6 := by
  obtain ⟨F, hF, hfinite, J, hc, _hconj, ⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv S e.toEquiv
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.OddFourProjectiveRank.psu_four_twoRank_le_six J
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hc)

/-- Every odd symplectic four-space central quotient has two-rank at most six. -/
theorem odd_psp_four_twoRank_le_six {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSp S 2 q) : primeRank 2 S ≤ 6 := by
  obtain ⟨F, hF, hfinite, hc, ⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.SymplecticFour.OddProjectiveRank.twoRank_le_six
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hc))

/-- All seven odd Theorem B rows have rank strictly below eight, with the
original field powers and Fermat or Mersenne conditions retained. -/
theorem IsTheoremBOddModel.twoRank_le_seven (hm : IsTheoremBOddModel S) :
    primeRank 2 S ≤ 7 := by
  cases hm with
  | linear_two q ho h => exact (odd_psl_two_twoRank_le_two ho h).trans (by decide)
  | linear_three p k _ ho _ h =>
      exact (odd_psl_three_twoRank_le_two ho.pow h).trans (by decide)
  | unitary_three p k _ ho _ h =>
      exact (odd_psu_three_twoRank_le_two ho.pow h).trans (by decide)
  | symplectic p _ ho h => exact (odd_psp_four_twoRank_le_six ho h).trans (by decide)
  | g2 p _ ho h => exact odd_g2_twoRank_le_seven ho h
  | linear_four r _ hf h =>
      have ho : Odd r := by
        obtain ⟨k,rfl⟩ := hf
        exact (even_two.pow_of_ne_zero (by positivity)).add_one
      exact (odd_psl_four_twoRank_le_six ho h).trans (by decide)
  | unitary_four s hp hm h =>
      have ho : Odd s := by
        obtain ⟨b, hb⟩ := hm
        have hb0 : b ≠ 0 := by
          intro he
          simp only [he, pow_zero] at hb
          have := hp.two_le
          omega
        have heven : Even (s + 1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
      exact (odd_psu_four_twoRank_le_six ho h).trans (by decide)

/-- Rank at least eight excludes the complete odd Theorem B family. -/
theorem no_theoremB_odd_model_of_twoRank_ge_eight (hr : 8 ≤ primeRank 2 S) :
    ¬ IsTheoremBOddModel S := by
  intro hm
  have := hm.twoRank_le_seven
  omega

end CFSG.Quasithin.ChapterA.Section02
