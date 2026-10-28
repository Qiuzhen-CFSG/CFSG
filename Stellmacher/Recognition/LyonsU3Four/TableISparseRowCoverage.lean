module

public import Stellmacher.Recognition.LyonsU3Four.TableISparseRowSupport

/-!
# Coverage of the sparse normalized rows

The vanishing opposite products force three of the last four entries to be
identical. The fourth differs from them by at most one. For such a row, write
`t, x` for its first two entries, `a` for the repeated entry, and `e` for the
exceptional offset. Completing squares in its contribution bounds each of
`t, x, a` between -3 and 3. A kernel-checked finite calculation then places
all admissible choices in the existing 85-row catalogue, preserving its indices.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Case 6.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.TableISparseRows
open scoped BigOperators

private theorem contribution_explicit (t x a b c d : ℤ) : contribution ![t, x, a, b, c, d] =
    4 * t^2 + x^2 + a^2 + b^2 + c^2 + d^2 +
    3 * ((x-a)^2 + (x-b)^2 + (a-b)^2 + (x-c)^2 + (a-c)^2 + (b-c)^2 +
      (x-d)^2 + (a-d)^2 + (b-d)^2 + (c-d)^2) := by
  have hi (i : Fin 5) : Finset.Iio i = Finset.univ.filter (· < i) := by
    ext j; simp
  simp [contribution, hi, Finset.sum_filter, Fin.sum_univ_succ]
  ring

private def shape (t x a e : ℤ) (k : Fin 4) : TableIRow :=
  ![![t, x, a, a, a, a+e], ![t, x, a+e, a, a, a],
    ![t, x, a, a+e, a, a], ![t, x, a, a, a+e, a]] k

private def q (t x a e : ℤ) : ℤ :=
  4 * t^2 + x^2 + 3 * a^2 + (a+e)^2 + 9 * (x-a)^2 + 3 * (x-a-e)^2 + 9 * e^2

private theorem q_bounds (t x a e : ℤ) (h : q t x a e < 64) :
    (-3 ≤ t ∧ t ≤ 3) ∧ (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ a ∧ a ≤ 3) := by
  dsimp [q] at h
  have ht : 4*t^2 < 64 := by
    nlinarith only [h, sq_nonneg x, sq_nonneg a, sq_nonneg (a+e),
      sq_nonneg (x-a), sq_nonneg (x-a-e), sq_nonneg e]
  have hx : 4*x^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (3*x-4*a-e), sq_nonneg e]
  have ha : 4*a^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (x+e), sq_nonneg (x-a),
      sq_nonneg (x-a-e), sq_nonneg e]
  constructor
  · constructor <;> nlinarith only [ht]
  constructor
  · constructor <;> nlinarith only [hx]
  · constructor <;> nlinarith only [ha]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem finite_coverage : ∀ t x a : Fin 7, ∀ e : Fin 3,
    q ((t:ℤ)-3) ((x:ℤ)-3) ((a:ℤ)-3) ((e:ℤ)-1) < 64 →
    Int.ModEq 4 ((t:ℤ)-3) (((x:ℤ)-3) + 4*((a:ℤ)-3) + ((e:ℤ)-1)) →
    0 < ((x:ℤ)-3) + 4*((a:ℤ)-3) + ((e:ℤ)-1) →
    ∀ k : Fin 4, ∃ j : Fin 85,
      shape ((t:ℤ)-3) ((x:ℤ)-3) ((a:ℤ)-3) ((e:ℤ)-1) k = row j := by
  decide

private theorem shape_contribution (t x a e : ℤ) (k : Fin 4) :
    contribution (shape t x a e k) = q t x a e := by
  fin_cases k <;> simp [shape, contribution_explicit, q] <;> ring

private theorem shape_z (t x a e : ℤ) (k : Fin 4) :
    z (shape t x a e k) = x + 4*a + e := by
  fin_cases k <;> simp [shape, z, Fin.sum_univ_succ] <;> ring

private theorem admissible_shape (r : TableIRow) (h : Admissible r) :
    ∃ t x a e : ℤ, ∃ k : Fin 4, (-1 ≤ e ∧ e ≤ 1) ∧ r = shape t x a e k := by
  have h0 := h.unit_bounds 0
  have h1 := h.unit_bounds 1
  have h2 := h.unit_bounds 2
  change -1 ≤ r 2 - r 3 ∧ r 2 - r 3 ≤ 1 at h0
  change -1 ≤ r 3 - r 4 ∧ r 3 - r 4 ≤ 1 at h1
  change -1 ≤ r 4 - r 5 ∧ r 4 - r 5 ≤ 1 at h2
  obtain ⟨h02, h13⟩ := h.opposite_zero
  change (r 2 - r 3) * (r 4 - r 5) = 0 at h02
  change (r 3 - r 4) * (r 5 - r 2) = 0 at h13
  rcases mul_eq_zero.mp h02 with ha | ha <;>
    rcases mul_eq_zero.mp h13 with hb | hb
  · refine ⟨r 0, r 1, r 2, r 5 - r 2, 0, ?_, ?_⟩
    · omega
    · funext i; fin_cases i <;> simp [shape] <;> omega
  · refine ⟨r 0, r 1, r 2, r 4 - r 2, 3, ?_, ?_⟩
    · omega
    · funext i; fin_cases i <;> simp [shape] <;> omega
  · refine ⟨r 0, r 1, r 3, r 2 - r 3, 1, ?_, ?_⟩
    · omega
    · funext i; fin_cases i <;> simp [shape] <;> omega
  · refine ⟨r 0, r 1, r 2, r 3 - r 2, 2, ?_, ?_⟩
    · omega
    · funext i; fin_cases i <;> simp [shape] <;> omega

private theorem bounded_seven (x : ℤ) (h : -3 ≤ x ∧ x ≤ 3) :
    ∃ k : Fin 7, x = (k : ℤ) - 3 := by
  refine ⟨⟨(x+3).toNat, by omega⟩, ?_⟩
  change x = ((x+3).toNat : ℤ) - 3
  omega

/-- Every admissible sparse row occurs in the fixed 85-row catalogue. -/
theorem admissible_covered (r : TableIRow) (h : Admissible r) :
    ∃ a : Fin 85, r = row a := by
  obtain ⟨t, x, a, e, k, he, hr⟩ := admissible_shape r h
  subst r
  have hc : q t x a e < 64 := by
    simpa only [shape_contribution] using h.contribution_lt
  obtain ⟨ht, hx, ha⟩ := q_bounds t x a e hc
  obtain ⟨t', rfl⟩ := bounded_seven t ht
  obtain ⟨x', rfl⟩ := bounded_seven x hx
  obtain ⟨a', rfl⟩ := bounded_seven a ha
  have he' : ∃ e' : Fin 3, e = (e' : ℤ) - 1 := by
    refine ⟨⟨(e+1).toNat, by omega⟩, ?_⟩
    change e = ((e+1).toNat : ℤ) - 1
    omega
  obtain ⟨e', rfl⟩ := he'
  apply finite_coverage t' x' a' e' hc _ _ k
  · have hz := h.congruence
    rw [shape_z] at hz
    convert hz using 1
    fin_cases k <;> rfl
  · simpa only [shape_z] using h.z_pos

end Stellmacher.Recognition.LyonsU3Four.TableISparseRows
