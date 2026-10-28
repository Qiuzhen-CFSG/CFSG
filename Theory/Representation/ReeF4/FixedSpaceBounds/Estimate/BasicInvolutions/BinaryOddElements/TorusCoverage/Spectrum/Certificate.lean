module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Tactic.FinCases

/-!
# A finite certificate for balanced F4 character counts

The twenty-four integral linear forms below are the evaluations of the published
short-root weight table. Reversing the coordinates and doubling the last two
weight coordinates evaluates the long-root table at `(2d, 2c, b, a)`.
`Spectrum` proves these identifications with the actual character counts.

We check all vectors whose first nonzero entry is one: 156 vectors modulo five
and 2380 modulo thirteen. Each check first accepts a short count at most four;
otherwise it verifies that the long count differs. The thirteen leading-coordinate
slices are checked separately by kernel reduction, with default resource limits.
No external computation or native evaluator is part of the proof.

Source: the F4 root tables of GLS3, Sections 1.8 and 1.14, used in the spectrum
step of Guralnick--Malle II, Lemma 8.8 (internal p.57).
-/

public section

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Spectrum

@[expose] def linearForms (a b c d : ℤ) : List ℤ :=
  [d, c - d, b - c, a - b + c, -a + c, a - c + d,
   -a + b - c + d, a - d, -b + c + d, -a + b - d,
   -c + 2 * d, -b + 2 * c - d,
   c - 2 * d, b - 2 * c + d, b - c - d, a - b + d,
   a - b + c - d, -a + d, -a + c - d, a - c,
   -a + b - c, -b + c, -c + d, -d]

@[expose] def shortCount (p : ℕ) (a b c d : ℤ) : ℕ :=
  (linearForms a b c d).countP (fun x : ℤ => x % (p : ℤ) == 0)

private abbrev CountCertificate (p : ℕ) (a b c d : ℤ) : Prop :=
  shortCount p a b c d ≤ 4 ∨
    shortCount p a b c d ≠ shortCount p (2 * d) (2 * c) b a

private theorem first_five : ∀ a b c : Fin 5,
    CountCertificate 5 1 a.val b.val c.val := by decide +kernel

private theorem second_five : ∀ b c : Fin 5,
    CountCertificate 5 0 1 b.val c.val := by decide +kernel

private theorem third_five : ∀ c : Fin 5,
    CountCertificate 5 0 0 1 c.val := by decide +kernel

private theorem fourth_five : CountCertificate 5 0 0 0 1 := by decide +kernel

private theorem first_thirteen : ∀ a b c : Fin 13,
    CountCertificate 13 1 a.val b.val c.val := by
  intro a
  fin_cases a <;> decide +kernel

private theorem second_thirteen : ∀ b c : Fin 13,
    CountCertificate 13 0 1 b.val c.val := by decide +kernel

private theorem third_thirteen : ∀ c : Fin 13,
    CountCertificate 13 0 0 1 c.val := by decide +kernel

private theorem fourth_thirteen : CountCertificate 13 0 0 0 1 := by decide +kernel

theorem balanced_normalized_le_four (p : ℕ) (hp : p = 5 ∨ p = 13)
    (a : Fin 4 → ℕ) (ha : ∀ i, a i < p)
    (hn : ∃ j : Fin 4, a j = 1 ∧ ∀ i, i < j → a i = 0) :
    shortCount p (a 0) (a 1) (a 2) (a 3) =
      shortCount p (2 * a 3) (2 * a 2) (a 1) (a 0) →
    shortCount p (a 0) (a 1) (a 2) (a 3) ≤ 4 := by
  have hc : CountCertificate p (a 0) (a 1) (a 2) (a 3) := by
    obtain ⟨j, hj, hprev⟩ := hn
    fin_cases j
    · change a 0 = 1 at hj
      rw [hj]
      rcases hp with rfl | rfl
      · exact first_five ⟨a 1, ha 1⟩ ⟨a 2, ha 2⟩ ⟨a 3, ha 3⟩
      · exact first_thirteen ⟨a 1, ha 1⟩ ⟨a 2, ha 2⟩ ⟨a 3, ha 3⟩
    · change a 1 = 1 at hj
      rw [hj, hprev 0 (by decide)]
      rcases hp with rfl | rfl
      · exact second_five ⟨a 2, ha 2⟩ ⟨a 3, ha 3⟩
      · exact second_thirteen ⟨a 2, ha 2⟩ ⟨a 3, ha 3⟩
    · change a 2 = 1 at hj
      rw [hj, hprev 0 (by decide), hprev 1 (by decide)]
      rcases hp with rfl | rfl
      · exact third_five ⟨a 3, ha 3⟩
      · exact third_thirteen ⟨a 3, ha 3⟩
    · change a 3 = 1 at hj
      rw [hj, hprev 0 (by decide), hprev 1 (by decide), hprev 2 (by decide)]
      rcases hp with rfl | rfl
      · exact fourth_five
      · exact fourth_thirteen
  intro hb
  rcases hc with hc | hc
  · exact hc
  · exact (hc hb).elim

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Spectrum
