module

public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRowSupport

/-!
# Exhaustive coverage of the isolated candidate rows

Completing squares in the contribution bounds every coordinate between -3 and 3.
For the five involution entries, their quadratic contribution is
`16 * ∑ xᵢ² - 3 * (∑ xᵢ)²`; subtracting four times any coordinate square
leaves a sum of squares. The isolated support condition has a finite formulation:
the difference row is one of four isolated patterns with either sign, or both
opposite sums vanish.

A kernel-checked enumeration, partitioned by the first coordinate, checks the
bounded rows against the original 89-row catalogue. Positivity and congruence
are tested before the quadratic inequality. All candidates are retained; global
multiplicity arguments belong to the consuming classification module.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Cases 2(b), 3 and 4 and Table I.
-/

public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows
open GeneralizedDecompositionData
private def q (t a b c d e : ℤ) : ℤ :=
  4*t^2 + 16*(a^2 + b^2 + c^2 + d^2 + e^2) - 3*(a+b+c+d+e)^2
private theorem contribution_explicit (r : TableIRow) :
    contribution r = q (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) := by
  have hi (i : Fin 5) : Finset.Iio i = Finset.univ.filter (· < i) := by
    ext j; simp
  simp [contribution, TableIPairedRows.contribution, q, hi, Finset.sum_filter,
    Fin.sum_univ_succ]
  ring
private theorem contribution_bounds (r : TableIRow) (h : contribution r < 64) :
    ∀ i, -3 ≤ r i ∧ r i ≤ 3 := by
  rw [contribution_explicit] at h
  dsimp [q] at h
  have h0 : 4*r 0^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 1),
      sq_nonneg (r 2),
      sq_nonneg (r 3),
      sq_nonneg (r 4),
      sq_nonneg (r 5),
      sq_nonneg (r 1-r 2),
      sq_nonneg (r 1-r 3),
      sq_nonneg (r 1-r 4),
      sq_nonneg (r 1-r 5),
      sq_nonneg (r 2-r 3),
      sq_nonneg (r 2-r 4),
      sq_nonneg (r 2-r 5),
      sq_nonneg (r 3-r 4),
      sq_nonneg (r 3-r 5),
      sq_nonneg (r 4-r 5)]
  have h1 : 4*r 1^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0),
      sq_nonneg (3*r 1-r 2-r 3-r 4-r 5),
      sq_nonneg (r 2-r 3),
      sq_nonneg (r 2-r 4),
      sq_nonneg (r 2-r 5),
      sq_nonneg (r 3-r 4),
      sq_nonneg (r 3-r 5),
      sq_nonneg (r 4-r 5)]
  have h2 : 4*r 2^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0),
      sq_nonneg (3*r 2-r 1-r 3-r 4-r 5),
      sq_nonneg (r 1-r 3),
      sq_nonneg (r 1-r 4),
      sq_nonneg (r 1-r 5),
      sq_nonneg (r 3-r 4),
      sq_nonneg (r 3-r 5),
      sq_nonneg (r 4-r 5)]
  have h3 : 4*r 3^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0),
      sq_nonneg (3*r 3-r 1-r 2-r 4-r 5),
      sq_nonneg (r 1-r 2),
      sq_nonneg (r 1-r 4),
      sq_nonneg (r 1-r 5),
      sq_nonneg (r 2-r 4),
      sq_nonneg (r 2-r 5),
      sq_nonneg (r 4-r 5)]
  have h4 : 4*r 4^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0),
      sq_nonneg (3*r 4-r 1-r 2-r 3-r 5),
      sq_nonneg (r 1-r 2),
      sq_nonneg (r 1-r 3),
      sq_nonneg (r 1-r 5),
      sq_nonneg (r 2-r 3),
      sq_nonneg (r 2-r 5),
      sq_nonneg (r 3-r 5)]
  have h5 : 4*r 5^2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0),
      sq_nonneg (3*r 5-r 1-r 2-r 3-r 4),
      sq_nonneg (r 1-r 2),
      sq_nonneg (r 1-r 3),
      sq_nonneg (r 1-r 4),
      sq_nonneg (r 2-r 3),
      sq_nonneg (r 2-r 4),
      sq_nonneg (r 3-r 4)]
  intro i
  fin_cases i
  · change -3 ≤ r 0 ∧ r 0 ≤ 3
    constructor <;> nlinarith only [h0]
  · change -3 ≤ r 1 ∧ r 1 ≤ 3
    constructor <;> nlinarith only [h1]
  · change -3 ≤ r 2 ∧ r 2 ≤ 3
    constructor <;> nlinarith only [h2]
  · change -3 ≤ r 3 ∧ r 3 ≤ 3
    constructor <;> nlinarith only [h3]
  · change -3 ≤ r 4 ∧ r 4 ≤ 3
    constructor <;> nlinarith only [h4]
  · change -3 ≤ r 5 ∧ r 5 ≤ 3
    constructor <;> nlinarith only [h5]

private def finiteSupport (r : TableIRow) : Prop :=
  (difference r 0 + difference r 2 = 0 ∧ difference r 1 + difference r 3 = 0) ∨
  ∃ k : Fin 4, difference r = isolatedDifferenceRow k ∨
    difference r = fun i => -isolatedDifferenceRow k i
private theorem admissible_finiteSupport (r : TableIRow) (h : Admissible r) :
    finiteSupport r := by
  rcases h.support with ⟨k, ε, he, hr⟩ | hs
  · right
    refine ⟨k, ?_⟩
    rcases sq_eq_one_iff.mp he with rfl | rfl
    · left; simpa using hr
    · right; simpa using hr
  · exact Or.inl hs
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem finite_coverage (t : Fin 7) : ∀ a b c d e : Fin 7,
    0 < ((a:ℤ)-3) + ((b:ℤ)-3) + ((c:ℤ)-3) + ((d:ℤ)-3) + ((e:ℤ)-3) →
    Int.ModEq 4 ((t:ℤ)-3)
      (((a:ℤ)-3) + ((b:ℤ)-3) + ((c:ℤ)-3) + ((d:ℤ)-3) + ((e:ℤ)-3)) →
    q ((t:ℤ)-3) ((a:ℤ)-3) ((b:ℤ)-3) ((c:ℤ)-3) ((d:ℤ)-3) ((e:ℤ)-3) < 64 →
    let r : TableIRow := ![(t:ℤ)-3, (a:ℤ)-3, (b:ℤ)-3, (c:ℤ)-3, (d:ℤ)-3, (e:ℤ)-3]
    finiteSupport r → ∃ j : Fin 89, r = row j := by
  unfold finiteSupport
  fin_cases t <;> decide +kernel

private theorem bounded_seven (x : ℤ) (h : -3 ≤ x ∧ x ≤ 3) :
    ∃ k : Fin 7, x = (k : ℤ) - 3 := by
  refine ⟨⟨(x+3).toNat, by omega⟩, ?_⟩
  change x = ((x+3).toNat : ℤ) - 3
  omega

/-- Every admissible isolated row occurs in the fixed 89-row catalogue. -/
theorem admissible_covered (r : TableIRow) (h : Admissible r) :
    ∃ a : Fin 89, r = row a := by
  have bounds := contribution_bounds r h.contribution_lt
  obtain ⟨t, ht⟩ := bounded_seven (r 0) (bounds 0)
  obtain ⟨a, ha⟩ := bounded_seven (r 1) (bounds 1)
  obtain ⟨b, hb⟩ := bounded_seven (r 2) (bounds 2)
  obtain ⟨c, hc⟩ := bounded_seven (r 3) (bounds 3)
  obtain ⟨d, hd⟩ := bounded_seven (r 4) (bounds 4)
  obtain ⟨e, he⟩ := bounded_seven (r 5) (bounds 5)
  have hr : r = ![(t:ℤ)-3, (a:ℤ)-3, (b:ℤ)-3, (c:ℤ)-3, (d:ℤ)-3, (e:ℤ)-3] := by
    funext i
    fin_cases i
    · exact ht
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
  have hz : z r = r 1+r 2+r 3+r 4+r 5 := by
    simp [z, TableIPairedRows.z, Fin.sum_univ_succ]
    ring
  have hp := h.z_pos
  have hm := h.congruence
  rw [hz] at hp hm
  have hq := h.contribution_lt
  rw [contribution_explicit] at hq
  have hs := admissible_finiteSupport r h
  rw [hr] at hp hm hq hs ⊢
  exact finite_coverage t a b c d e hp hm hq hs
end Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRows
