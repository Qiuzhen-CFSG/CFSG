module

public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-!
# The degree calculation in Lyons's surviving cases

This file records the arithmetic at the end of Lyons's Table I calculation.
The signed rows are represented by their integer degrees.  The inequalities,
congruence enumeration, and Schur exclusions used before the last two displayed
equations are deliberately packaged as fields of the two records below.  This
keeps the numerical interface independent of the eventual character-realisation
proof, while the consequences of those fields are proved here.

The equations are Lyons (U1)--(U3) and their case (V) analogues, p. 386.
The common final weighted-column calculation is imported from
`TableISurvivorArithmetic`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four

/-! The two equations used after the preceding Table I exclusions. -/

def survivorU1 (x1 x3 x4 x5 x6 : ℤ) : Prop :=
  (1 : ℚ) - 36 / x1 + 4 / x3 - 98 / x4 + 200 / x5 + 1 / x6 = 0

def survivorU2 (x1 x2 x3 x4 x6 x7 : ℤ) : Prop :=
  (1 : ℚ) + 18 / x1 + 16 / x2 - 1 / x3 - 49 / x4 + 1 / x6 - 16 / x7 = 0

def survivorU3 (x1 x2 x4 x5 x6 : ℤ) : Prop :=
  (0 : ℚ) < 1 + 36 / x1 + 64 / x2 + 98 / x4 + 200 / x5 + 1 / x6

/-- Public equation interfaces for constructing prefixes in extension modules. -/
theorem survivorU1_iff (x1 x3 x4 x5 x6 : ℤ) :
    survivorU1 x1 x3 x4 x5 x6 ↔
      (1 : ℚ) - 36 / x1 + 4 / x3 - 98 / x4 + 200 / x5 + 1 / x6 = 0 := Iff.rfl

theorem survivorU2_iff (x1 x2 x3 x4 x6 x7 : ℤ) :
    survivorU2 x1 x2 x3 x4 x6 x7 ↔
      (1 : ℚ) + 18 / x1 + 16 / x2 - 1 / x3 - 49 / x4 + 1 / x6 - 16 / x7 = 0 := Iff.rfl

theorem survivorU3_iff (x1 x2 x4 x5 x6 : ℤ) :
    survivorU3 x1 x2 x4 x5 x6 ↔
      (0 : ℚ) < 1 + 36 / x1 + 64 / x2 + 98 / x4 + 200 / x5 + 1 / x6 := Iff.rfl

/-! The finite residue alternatives are the output of the congruence and
Schur-prime elimination in the preceding pages of the paper.  They are stated
as alternatives, rather than hidden in a tactic, so that callers can discharge
them directly from `DegreeConstraints` and `PrimeConstraints`. -/

structure UPrefix where
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ
  x6 : ℤ
  x7 : ℤ
  h1 : survivorU1 x1 x3 x4 x5 x6
  h2 : survivorU2 x1 x2 x3 x4 x6 x7
  h3 : survivorU3 x1 x2 x4 x5 x6
  hx1 : x1 = -13
  hx4 : x4 = 39
  hx5 : x5 = -150
  hx3x6 : x3 = x6
  hx2 : x2 = 52 ∨ x2 = -12
  hne3 : x3 ≠ 0
  hne6 : x6 ≠ 0
  hne7 : x7 ≠ 0
  hpair_eq : (4 : ℚ) / x3 + 1 / x6 = 1 / 13
  hx2_not_neg : x2 ≠ -12

structure VPrefix where
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x6 : ℤ
  x7 : ℤ
  middle : Fin 4 → ℤ
  h1 : (1 : ℚ) - 36 / x1 + 4 / x3 - 98 / x4 +
    (∑ i, 25 / (middle i : ℚ)) + 1 / x6 = 0
  h2 : survivorU2 x1 x2 x3 x4 x6 x7
  h3 : (0 : ℚ) < 1 + 36 / x1 + 64 / x2 + 98 / x4 +
    (∑ i, 25 / (middle i : ℚ)) + 1 / x6
  hx1 : x1 = -13
  hx4 : x4 = 39
  hx3x6 : x3 = x6
  hx2 : x2 = 52 ∨ x2 = -12
  hmiddle : ∀ i, middle i = -75
  hne3 : x3 ≠ 0
  hne6 : x6 ≠ 0
  hne7 : x7 ≠ 0
  hpair_eq : (4 : ℚ) / x3 + 1 / x6 = 1 / 13
  hx2_not_neg : x2 ≠ -12

theorem survivorU_x3_x6 (h : UPrefix) : h.x3 = 65 ∧ h.x6 = 65 := by
  have heq := h.hpair_eq
  rw [h.hx3x6] at heq
  have heq' : (5 : ℚ) / h.x6 = 1 / 13 := by
    calc
      (5 : ℚ) / h.x6 = 4 / h.x6 + 1 / h.x6 := by ring
      _ = 1 / 13 := heq
  have hx6 : (h.x6 : ℚ) = 65 := by
    field_simp [h.hne6] at heq'
    linarith
  have hx3 : (h.x3 : ℚ) = 65 := by simpa [h.hx3x6] using hx6
  constructor
  · exact_mod_cast hx3
  · exact_mod_cast hx6

theorem survivorU_x2 (h : UPrefix) : h.x2 = 52 := by
  rcases h.hx2 with h52 | hm12
  · exact h52
  · exfalso
    exact h.hx2_not_neg hm12

theorem survivorU_x7 (h : UPrefix) : h.x7 = -12 := by
  have hx36 := survivorU_x3_x6 h
  have hx2 := survivorU_x2 h
  have hh := h.h2
  rw [h.hx1, hx2, hx36.1, h.hx4, hx36.2] at hh
  simp [survivorU2] at hh
  field_simp [h.hne7] at hh
  have hx : (h.x7 : ℚ) = -12 := by linarith
  exact_mod_cast hx

theorem survivorU_forced (h : UPrefix) :
    h.x1 = -13 ∧ h.x2 = 52 ∧ h.x3 = 65 ∧ h.x4 = 39 ∧
      h.x5 = -150 ∧ h.x6 = 65 ∧ h.x7 = -12 := by
  have h36 := survivorU_x3_x6 h
  exact ⟨h.hx1, survivorU_x2 h, h36.1, h.hx4, h.hx5, h36.2,
    survivorU_x7 h⟩

theorem survivorU_middle_value (h : UPrefix) :
    (200 : ℚ) / h.x5 = -4 / 3 := by
  rw [h.hx5]
  norm_num

theorem survivorU_order (h : UPrefix) (g c e : ℕ)
    (hL : (g : ℚ) * e ^ 2 *
      (1 + 36 / (-13 : ℚ) + 64 / 52 + 98 / 39 +
        (200 : ℚ) / h.x5 + 1 / 65) = 128 * c ^ 3) :
    g * e ^ 2 = 195 * c ^ 3 := by
  have hm := survivorU_middle_value h
  have hL' : (g : ℚ) * e ^ 2 *
      (1 + 36 / (-13 : ℚ) + 64 / 52 + 98 / 39 +
        (200 : ℚ) / h.x5 + 1 / 65) = 128 * c ^ 3 := hL
  rw [hm] at hL'
  have he : (g : ℚ) * e ^ 2 = 195 * c ^ 3 := by
    norm_num at hL' ⊢
    linarith
  exact_mod_cast he

theorem survivorV_middle (h : VPrefix) (i : Fin 4) : h.middle i = -75 :=
  h.hmiddle i

theorem survivorV_x3_x6 (h : VPrefix) : h.x3 = 65 ∧ h.x6 = 65 := by
  have heq := h.hpair_eq
  rw [h.hx3x6] at heq
  have heq' : (5 : ℚ) / h.x6 = 1 / 13 := by
    calc
      (5 : ℚ) / h.x6 = 4 / h.x6 + 1 / h.x6 := by ring
      _ = 1 / 13 := heq
  field_simp [h.hne6] at heq'
  have hx6 : (h.x6 : ℚ) = 65 := by linarith
  have hx3 : (h.x3 : ℚ) = 65 := by simpa [h.hx3x6] using hx6
  exact ⟨by exact_mod_cast hx3, by exact_mod_cast hx6⟩

theorem survivorV_x2 (h : VPrefix) : h.x2 = 52 := by
  rcases h.hx2 with h52 | hm12
  · exact h52
  · exfalso
    exact h.hx2_not_neg hm12

theorem survivorV_x7 (h : VPrefix) : h.x7 = -12 := by
  have hx36 := survivorV_x3_x6 h
  have hx2 := survivorV_x2 h
  have hh := h.h2
  rw [h.hx1, hx2, hx36.1, h.hx4, hx36.2] at hh
  simp [survivorU2] at hh
  field_simp [h.hne7] at hh
  have hx : (h.x7 : ℚ) = -12 := by linarith
  exact_mod_cast hx

theorem survivorV_forced (h : VPrefix) :
    h.x1 = -13 ∧ h.x2 = 52 ∧ h.x3 = 65 ∧ h.x4 = 39 ∧
      (∀ i, h.middle i = -75) ∧ h.x6 = 65 ∧ h.x7 = -12 := by
  have h36 := survivorV_x3_x6 h
  exact ⟨h.hx1, survivorV_x2 h, h36.1, h.hx4, h.hmiddle,
    h36.2, survivorV_x7 h⟩

theorem survivorV_middle_value (h : VPrefix) :
    (∑ i, 25 / (h.middle i : ℚ)) = -4 / 3 := by
  simp_rw [h.hmiddle]
  norm_num

theorem survivorV_order (h : VPrefix) (g c e : ℕ)
    (hL : (g : ℚ) * e ^ 2 *
      (1 + 36 / (-13 : ℚ) + 64 / 52 + 98 / 39 +
        (∑ i, 25 / (h.middle i : ℚ)) + 1 / 65) = 128 * c ^ 3) :
    g * e ^ 2 = 195 * c ^ 3 := by
  have hm := survivorV_middle_value h
  rw [hm] at hL
  have he : (g : ℚ) * e ^ 2 = 195 * c ^ 3 := by
    norm_num at hL ⊢
    linarith
  exact_mod_cast he

/-! The final extraction contract.  `degreeTwelve` records the row identified
by the Table I matrix, and `weight_identity` is the direct finite sum obtained
from that matrix.  The conclusion is the unique degree-twelve row together
with the numerical value needed by Lemma 4(c). -/

structure DegreeTwelveWitness {I : Type*} [Fintype I]
    (d : GeneralizedDecompositionData I) (degree : I → ℤ) where
  row : I
  abs_degree : (degree row).natAbs = 12
  unique : ∀ j, (degree j).natAbs = 12 → j = row
  weight_identity : d.weightedColumn degree (d.iDz 0) = 128 / 195

theorem degreeTwelve_unique {I : Type*} [Fintype I]
    {d : GeneralizedDecompositionData I} {degree : I → ℤ}
    (w : DegreeTwelveWitness d degree) :
    ∃! j, (degree j).natAbs = 12 := by
  refine ⟨w.row, w.abs_degree, ?_⟩
  intro y hy
  exact w.unique y hy

theorem degreeTwelve_weight {I : Type*} [Fintype I]
    {d : GeneralizedDecompositionData I} {degree : I → ℤ}
    (w : DegreeTwelveWitness d degree) :
    d.weightedColumn degree (d.iDz 0) = 128 / 195 :=
  w.weight_identity

end Stellmacher.Recognition.LyonsU3Four
