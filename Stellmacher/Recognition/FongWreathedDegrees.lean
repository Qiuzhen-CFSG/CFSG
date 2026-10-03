module

public import Stellmacher.Recognition.FongWreathedDegreeConstraints
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The exact degree calculation for Fong's rational characters

The numerical conditions force the three rows to be `(27, 3, -1, 3)`,
`(21, 5, 1, 1)`, and `(7, -1, -1, 3)`, with the last two interchangeable.
This is an arithmetic implication; the character-theoretic premises are
represented by `FongDegreeConditions`.

Equation (9) bounds one negative-constituent degree by fifty. For each of
its possible residues and each pair of odd involution values, the other
(unbounded) degree is an integer root of the quadratic already established
in `FongWreathedDegreeConstraints`. The quadratic formula, including its
linear case, reduces the calculation to two root choices. Kernel reduction
checks the resulting finite table of thirteen possibilities. The remaining
congruences and square bound leave degrees 27 and 35; Sylow restriction
excludes 35 and fixes the values at the central order-four classes.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), pp. 69–74, and the completion of its omitted
calculation in `refs/original/n-group-global/sylow32-source-audit/
fong-degree-calculation-audit.md`.
-/

namespace Stellmacher.Recognition

private def rootValue (A B C : ℤ) (i : Fin 2) : ℤ :=
  if A = 0 then -C / B else
    (-B + (if i = 0 then 1 else -1) * Int.sqrt (B ^ 2 - 4 * A * C)) / (2 * A)

private theorem eq_rootValue (A B C t : ℤ) (hC : C ≠ 0)
    (h : A * t ^ 2 + B * t + C = 0) : ∃ i : Fin 2, t = rootValue A B C i := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := by intro hb; simp [hA, hb] at h; exact hC h
    have he : -C = B * t := by simp only [hA, zero_mul, zero_add] at h; linarith
    exact ⟨0, by simp [rootValue, hA, he, Int.mul_ediv_cancel_left _ hB]⟩
  · have hD : B ^ 2 - 4 * A * C = (2 * A * t + B) * (2 * A * t + B) := by
      linear_combination -4 * A * h
    have hs : Int.sqrt (B ^ 2 - 4 * A * C) = |2 * A * t + B| := by
      rw [hD, Int.sqrt_eq, Int.natCast_natAbs]
    have h2A : 2 * A ≠ 0 := mul_ne_zero (by decide) hA
    by_cases ht : 0 ≤ 2 * A * t + B
    · rw [abs_of_nonneg ht] at hs
      have he : -B + Int.sqrt (B ^ 2 - 4 * A * C) = 2 * A * t := by rw [hs]; ring
      exact ⟨0, by simp [rootValue, hA, he, Int.mul_ediv_cancel_left _ h2A]⟩
    · rw [abs_of_neg (lt_of_not_ge ht)] at hs
      have he : -B - Int.sqrt (B ^ 2 - 4 * A * C) = 2 * A * t := by rw [hs]; ring
      exact ⟨1, by simp [rootValue, hA, ← sub_eq_add_neg, he, Int.mul_ediv_cancel_left _ h2A]⟩

private def coarseValid (d s t a b c : ℤ) : Prop :=
  |a| ≤ 5 ∧ |a| < d ∧ |b| < s ∧ |c| < t ∧
  d % 8 = a % 8 ∧ s % 8 = b % 8 ∧ t % 8 = c % 8 ∧
  (s - b ^ 2) * t ^ 2 +
    (s * (s - 1) + a ^ 2 * s - b ^ 2 * (s - 1) - c ^ 2 * s) * t -
      c ^ 2 * s * (s - 1) = 0

private instance (d s t a b c : ℤ) : Decidable (coarseValid d s t a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def coarseTable : Finset (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {(27, 7, 21, 3, -1, 5), (27, 21, 7, 3, 5, -1),
   (35, 15, 21, 3, -1, 5), (35, 21, 15, 3, 5, -1),
   (39, 13, 27, -1, -3, 3), (39, 27, 13, -1, 3, -3),
   (55, 11, 45, -1, 3, -3), (55, 45, 11, -1, -3, 3),
   (75, 19, 57, -5, -5, 1), (111, 37, 75, -1, 5, -5),
   (119, 35, 85, -1, -5, 5), (125, 21, 105, 5, 5, 1),
   (351, 27, 325, -1, -5, 5)}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem finite_coarse_table :
    ∀ (ib ic : Fin 6) (is : Fin 7) (ir : Fin 2),
      let b : ℤ := 2 * ib.val - 5
      let c : ℤ := 2 * ic.val - 5
      let a := b + c - 1
      let s : ℤ := 8 * is.val + b
      let t := rootValue (s - b ^ 2)
          (s * (s - 1) + a ^ 2 * s - b ^ 2 * (s - 1) - c ^ 2 * s)
          (-c ^ 2 * s * (s - 1)) ir

      |b| < s → s ≤ 50 → s % 8 = b % 8 → coarseValid (s + t - 1) s t a b c →
        (s + t - 1, s, t, a, b, c) ∈ coarseTable := by
  intro ib ic
  fin_cases ib <;> fin_cases ic <;> intro is <;> fin_cases is <;>
    intro ir <;> fin_cases ir <;>
    decide +kernel

private theorem mem_coarse_table {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) (hs : r₃.d ≤ 50) :
    (r₂.d, r₃.d, r₄.d, r₂.a, r₃.a, r₄.a) ∈ coarseTable := by
  have hb := h.row₃.involution_bound
  have hc := h.row₄.involution_bound
  rw [abs_le] at hb hc
  have hbo := Int.odd_iff.mp h.row₃.involution_odd
  have hco := Int.odd_iff.mp h.row₄.involution_odd
  let ib : Fin 6 := ⟨((r₃.a + 5) / 2).toNat, by omega⟩
  let ic : Fin 6 := ⟨((r₄.a + 5) / 2).toNat, by omega⟩
  have hsc := h.row₃.degree_congr
  have hsg := h.row₃.degree_gt
  let is : Fin 7 := ⟨((r₃.d - r₃.a) / 8).toNat, by omega⟩
  have hb' : (2 * ib.val : ℤ) - 5 = r₃.a := by dsimp [ib]; omega
  have hc' : (2 * ic.val : ℤ) - 5 = r₄.a := by dsimp [ic]; omega
  have hsp := h.row₃.degree_pos
  have hs' : (8 * is.val : ℤ) + r₃.a = r₃.d := by dsimp [is]; rw [abs_lt] at hsg; omega
  have ha' : r₃.a + r₄.a - 1 = r₂.a := by linarith [h.involution_sum]
  have hd' : r₃.d + r₄.d - 1 = r₂.d := by linarith [h.degree_sum]
  have hC : -r₄.a ^ 2 * r₃.d * (r₃.d - 1) ≠ 0 := by
    have ha4 : r₄.a ≠ 0 := by omega
    have hs1 : r₃.d - 1 ≠ 0 := by
      have hgt := h.row₃.degree_gt
      rw [abs_lt] at hgt
      omega
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ha4))
      (ne_of_gt hsp)) hs1
  obtain ⟨ir, hir⟩ := eq_rootValue (r₃.d - r₃.a ^ 2)
    (r₃.d * (r₃.d - 1) + r₂.a ^ 2 * r₃.d - r₃.a ^ 2 * (r₃.d - 1) - r₄.a ^ 2 * r₃.d)
    _ r₄.d hC (by simpa only [sub_eq_add_neg, neg_mul] using h.quadratic)
  have hf := finite_coarse_table ib ic is ir
  dsimp only at hf
  rw [hb', hc', hs', ha'] at hf
  have hv : coarseValid (r₃.d + r₄.d - 1) r₃.d r₄.d r₂.a r₃.a r₄.a := by
    rw [hd']
    exact ⟨h.row₂.involution_bound, h.row₂.degree_gt, h.row₃.degree_gt, h.row₄.degree_gt,
      h.row₂.degree_congr, h.row₃.degree_congr, h.row₄.degree_congr, h.quadratic⟩
  rw [← hir] at hf
  simpa only [hd'] using hf h.row₃.degree_gt hs h.row₃.degree_congr hv

private theorem b_bounds {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) :
    (-3 ≤ r₂.b ∧ r₂.b ≤ 3) ∧ (-3 ≤ r₃.b ∧ r₃.b ≤ 3) ∧ (-3 ≤ r₄.b ∧ r₄.b ≤ 3) := by
  have hb := h.orderFour_square_bound
  have h₂ := sq_nonneg r₂.b
  have h₃ := sq_nonneg r₃.b
  have h₄ := sq_nonneg r₄.b
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

private theorem value_of_restriction (b d a f : ℤ) (hb : -3 ≤ b ∧ b ≤ 3)
    (h : (d - 2 * a + 7 * b + 2 * f) % 8 = 0) :
    b = (d - 2 * a + 2 * f + 3) % 8 - 3 := by omega

private theorem coarse_of_small {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) (hs : r₃.d ≤ 50) :
    ((r₂.d, r₂.a, r₂.b) = (27, 3, -1) ∧
      (((r₃.d, r₃.a, r₃.b) = (21, 5, 1) ∧ (r₄.d, r₄.a, r₄.b) = (7, -1, -1)) ∨
       ((r₄.d, r₄.a, r₄.b) = (21, 5, 1) ∧ (r₃.d, r₃.a, r₃.b) = (7, -1, -1)))) ∨
    (r₂.d, r₂.a, r₂.b) = (35, 3, -1) := by
  have hm := mem_coarse_table h hs
  have hb := b_bounds h
  have h₂ := value_of_restriction _ _ _ _ hb.1 h.row₂.restriction_congr
  have h₃ := value_of_restriction _ _ _ _ hb.2.1 h.row₃.restriction_congr
  have h₄ := value_of_restriction _ _ _ _ hb.2.2 h.row₄.restriction_congr
  have hsum := h.orderFour_square_bound
  clear h hs hb
  simp only [coarseTable, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  all_goals
    rcases hm with ⟨hd₂, hd₃, hd₄, ha₂, ha₃, ha₄⟩
    norm_num [hd₂, hd₃, hd₄, ha₂, ha₃, ha₄] at h₂ h₃ h₄
    norm_num [h₂, h₃, h₄] at hsum
    all_goals norm_num [hd₂, hd₃, hd₄, ha₂, ha₃, ha₄, h₂, h₃, h₄]

private theorem rows_of_small {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) (hs : r₃.d ≤ 50) :
    r₂ = ⟨27, 3, -1, 3⟩ ∧
      ((r₃ = ⟨21, 5, 1, 1⟩ ∧ r₄ = ⟨7, -1, -1, 3⟩) ∨
       (r₄ = ⟨21, 5, 1, 1⟩ ∧ r₃ = ⟨7, -1, -1, 3⟩)) := by
  rcases coarse_of_small h hs with ⟨h₂, ⟨h₃, h₄⟩ | ⟨h₄, h₃⟩⟩ | h₂
  · obtain ⟨he₂, he₃, he₄⟩ := h.rows_of_candidate27 h₂ h₃ h₄
    exact ⟨he₂, Or.inl ⟨he₃, he₄⟩⟩
  · obtain ⟨he₂, he₄, he₃⟩ := h.swap.rows_of_candidate27 h₂ h₄ h₃
    exact ⟨he₂, Or.inr ⟨he₄, he₃⟩⟩
  · exact False.elim (h.not_candidate35 h₂)

/-- The unique numerical character rows, up to exchange of the last two. -/
public theorem FongDegreeConditions.classification {r₂ r₃ r₄ : FongCharacterRow}
    (h : FongDegreeConditions r₂ r₃ r₄) :
    r₂ = ⟨27, 3, -1, 3⟩ ∧
      ((r₃ = ⟨21, 5, 1, 1⟩ ∧ r₄ = ⟨7, -1, -1, 3⟩) ∨
       (r₄ = ⟨21, 5, 1, 1⟩ ∧ r₃ = ⟨7, -1, -1, 3⟩)) := by
  rcases h.small_degree with hs | ht
  · exact rows_of_small h hs
  · obtain ⟨h₂, h34⟩ := rows_of_small h.swap ht
    exact ⟨h₂, h34.symm⟩

end Stellmacher.Recognition
