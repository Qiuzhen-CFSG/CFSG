module

public import Stellmacher.Recognition.LyonsU3Four.TableIPatterns
public import Stellmacher.Recognition.LyonsU3Four.TableIOrderPositivity
import Mathlib.Tactic

/-!
# Explicit matrices for the late cases of Lyons's Table I

These are the full integer matrices M, N, P, Q, R, S and T, including
all repeated rows. `degree x` assigns the signed degree labels printed in
the table, with `x 0` the principal degree. This is a concrete numerical
model, not an assertion that the existing abstract `TableIPattern` implies
this model. A classification with signed degree transport must supply that
bridge, including the repeated Galois labels.

Expanding the finite sums proves the weighted-column and orthogonality
identities used in the eliminations. In particular, no displayed equation
or bound is assumed independently of the actual matrix constraints.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Table I,
pp. 375–377, and eliminations pp. 384–385. Entries checked against page images.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

/-- The signed form of Lemma 5 for a nonprincipal degree, with
`b = 3 * χ(z) + 60 * dᵗ`. Both integrality and the multiplicity sign matter. -/
structure LateSignedDegree (x b : ℤ) : Prop where
  lower : 12 ≤ x.natAbs
  integral : Int.ModEq 64 (x + b) 0
  nonneg : 0 ≤ x * (x + b)

namespace LateM

/-- Full M matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 21 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-1, 3, 3, 3, 3, 3], ![1, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 21) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 21 → Fin 9 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8]

def degree (x : Fin 9 → ℤ) : Fin 21 → ℤ := fun j => x (label j)

def offset : Fin 9 → ℤ := ![63, 63, 63, 63, 12, -15, 63, 63, 12]

def representative : Fin 9 → Fin 21 := ![0, 1, 5, 9, 13, 17, 18, 19, 20]

theorem signed_degree {x : Fin 9 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 9) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (4 : ℚ) / (x 1) + (4 : ℚ) / (x 2) + (4 : ℚ) / (x 3) + (-225 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (1 : ℚ) / (x 7)

theorem tValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (4 : ℤ) * (x 2) + (4 : ℤ) * (x 3) + (-1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem tInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (64 : ℚ) / (x 4) + (675 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (1 : ℚ) / (x 7)

theorem zValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 4) + (3 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem zInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 1) + (1 : ℚ) / (x 2) + (1 : ℚ) / (x 3) + (48 : ℚ) / (x 4) + (675 : ℚ) / (x 5) + (16 : ℚ) / (x 8)

theorem wValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 1) + (1 : ℤ) * (x 2) + (1 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (3 : ℤ) * (x 5) + (1 : ℤ) * (x 8)

theorem wInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateM

namespace LateN

/-- Full N matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 21 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-2, 2, 2, 2, 2, 2], ![1, 1, 0, 0, 0, 0], ![1, 1, 2, 2, 2, 2], ![1, 1, 0, 0, 0, 0]]

def data : GeneralizedDecompositionData (Fin 21) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 21 → Fin 9 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8]

def degree (x : Fin 9 → ℤ) : Fin 21 → ℤ := fun j => x (label j)

def offset : Fin 9 → ℤ := ![63, 63, 63, 12, 12, -90, 63, 87, 63]

def representative : Fin 9 → Fin 21 := ![0, 1, 5, 9, 13, 17, 18, 19, 20]

theorem signed_degree {x : Fin 9 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 9) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (4 : ℚ) / (x 1) + (4 : ℚ) / (x 2) + (-200 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (81 : ℚ) / (x 7) + (1 : ℚ) / (x 8)

theorem tValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (4 : ℤ) * (x 2) + (-2 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8)

theorem tInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (64 : ℚ) / (x 3) + (64 : ℚ) / (x 4) + (200 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (81 : ℚ) / (x 7) + (1 : ℚ) / (x 8)

theorem zValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 3) + (4 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8)

theorem zInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 1) + (1 : ℚ) / (x 2) + (48 : ℚ) / (x 3) + (48 : ℚ) / (x 4) + (200 : ℚ) / (x 5) + (162 : ℚ) / (x 7)

theorem wValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 1) + (1 : ℤ) * (x 2) + (3 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (2 : ℤ) * (x 7)

theorem wInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateN

namespace LateP

/-- Full P matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 23 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-2, 2, 2, 2, 2, 2], ![1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 23) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 23 → Fin 11 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8, 9, 10]

def degree (x : Fin 11 → ℤ) : Fin 23 → ℤ := fun j => x (label j)

def offset : Fin 11 → ℤ := ![63, 63, 63, 12, 12, -90, 63, 75, 75, 12, 12]

def representative : Fin 11 → Fin 23 := ![0, 1, 5, 9, 13, 17, 18, 19, 20, 21, 22]

theorem signed_degree {x : Fin 11 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 11) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (4 : ℚ) / (x 1) + (4 : ℚ) / (x 2) + (-200 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (25 : ℚ) / (x 7) + (25 : ℚ) / (x 8)

theorem tValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (4 : ℤ) * (x 2) + (-2 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8)

theorem tInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (64 : ℚ) / (x 3) + (64 : ℚ) / (x 4) + (200 : ℚ) / (x 5) + (1 : ℚ) / (x 6) + (25 : ℚ) / (x 7) + (25 : ℚ) / (x 8)

theorem zValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 3) + (4 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8)

theorem zInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 1) + (1 : ℚ) / (x 2) + (48 : ℚ) / (x 3) + (48 : ℚ) / (x 4) + (200 : ℚ) / (x 5) + (25 : ℚ) / (x 7) + (25 : ℚ) / (x 8) + (16 : ℚ) / (x 9) + (16 : ℚ) / (x 10)

theorem wValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 1) + (1 : ℤ) * (x 2) + (3 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8) + (1 : ℤ) * (x 9) + (1 : ℤ) * (x 10)

theorem wInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateP

namespace LateQ

/-- Full Q matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 21 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-3, 1, 1, 1, 1, 1], ![1, 1, 2, 2, 2, 2], ![1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 21) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 21 → Fin 9 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8]

def degree (x : Fin 9 → ℤ) : Fin 21 → ℤ := fun j => x (label j)

def offset : Fin 9 → ℤ := ![63, 63, 12, 12, 12, -165, 87, 63, 12]

def representative : Fin 9 → Fin 21 := ![0, 1, 5, 9, 13, 17, 18, 19, 20]

theorem signed_degree {x : Fin 9 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 9) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (4 : ℚ) / (x 1) + (-75 : ℚ) / (x 5) + (81 : ℚ) / (x 6) + (1 : ℚ) / (x 7)

theorem tValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (-3 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem tInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (64 : ℚ) / (x 2) + (64 : ℚ) / (x 3) + (64 : ℚ) / (x 4) + (25 : ℚ) / (x 5) + (81 : ℚ) / (x 6) + (1 : ℚ) / (x 7)

theorem zValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 2) + (4 : ℤ) * (x 3) + (4 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem zInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 1) + (48 : ℚ) / (x 2) + (48 : ℚ) / (x 3) + (48 : ℚ) / (x 4) + (25 : ℚ) / (x 5) + (162 : ℚ) / (x 6) + (16 : ℚ) / (x 8)

theorem wValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 1) + (3 : ℤ) * (x 2) + (3 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (2 : ℤ) * (x 6) + (1 : ℤ) * (x 8)

theorem wInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateQ

namespace LateR

/-- Full R matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 23 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-3, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 23) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 23 → Fin 11 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8, 9, 10]

def degree (x : Fin 11 → ℤ) : Fin 23 → ℤ := fun j => x (label j)

def offset : Fin 11 → ℤ := ![63, 63, 12, 12, 12, -165, 75, 75, 12, 12, 12]

def representative : Fin 11 → Fin 23 := ![0, 1, 5, 9, 13, 17, 18, 19, 20, 21, 22]

theorem signed_degree {x : Fin 11 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 11) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (4 : ℚ) / (x 1) + (-75 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7)

theorem tValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (-3 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem tInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (64 : ℚ) / (x 2) + (64 : ℚ) / (x 3) + (64 : ℚ) / (x 4) + (25 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7)

theorem zValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 2) + (4 : ℤ) * (x 3) + (4 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem zInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 11 → ℤ) : ℚ :=
  (1 : ℚ) / (x 1) + (48 : ℚ) / (x 2) + (48 : ℚ) / (x 3) + (48 : ℚ) / (x 4) + (25 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7) + (16 : ℚ) / (x 8) + (16 : ℚ) / (x 9) + (16 : ℚ) / (x 10)

theorem wValue_eq (x : Fin 11 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 11 → ℤ) : ℤ :=
  (1 : ℤ) * (x 1) + (3 : ℤ) * (x 2) + (3 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8) + (1 : ℤ) * (x 9) + (1 : ℤ) * (x 10)

theorem wInner_eq (x : Fin 11 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateR

namespace LateS

/-- Full S matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 19 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![-1, 1, 1, 1, 0, 0], ![-1, 1, 1, 0, 0, 1], ![-1, 1, 0, 0, 1, 1], ![-1, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![-2, 0, 1, 0, 1, 0], ![-2, 0, 0, 1, 0, 1], ![1, 1, 2, 2, 2, 2], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 19) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 19 → Fin 9 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 6, 7, 8]

def degree (x : Fin 9 → ℤ) : Fin 19 → ℤ := fun j => x (label j)

def offset : Fin 9 → ℤ := ![63, -51, 12, 12, -114, 87, 75, 75, 12]

def representative : Fin 9 → Fin 19 := ![0, 1, 5, 9, 13, 15, 16, 17, 18]

theorem signed_degree {x : Fin 9 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 9) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (-36 : ℚ) / (x 1) + (-16 : ℚ) / (x 4) + (81 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7)

theorem tValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (-4 : ℤ) * (x 1) + (-4 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem tInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 9 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (36 : ℚ) / (x 1) + (64 : ℚ) / (x 2) + (64 : ℚ) / (x 3) + (81 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7)

theorem zValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 9 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (4 : ℤ) * (x 2) + (4 : ℤ) * (x 3) + (1 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7)

theorem zInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 9 → ℤ) : ℚ :=
  (18 : ℚ) / (x 1) + (48 : ℚ) / (x 2) + (48 : ℚ) / (x 3) + (4 : ℚ) / (x 4) + (162 : ℚ) / (x 5) + (25 : ℚ) / (x 6) + (25 : ℚ) / (x 7) + (16 : ℚ) / (x 8)

theorem wValue_eq (x : Fin 9 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 9 → ℤ) : ℤ :=
  (2 : ℤ) * (x 1) + (3 : ℤ) * (x 2) + (3 : ℤ) * (x 3) + (1 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (1 : ℤ) * (x 6) + (1 : ℤ) * (x 7) + (1 : ℤ) * (x 8)

theorem wInner_eq (x : Fin 9 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateS

namespace LateT

/-- Full T matrix in the order `dᵗ, ₁dᶻ, …, ₅dᶻ`. -/
def matrix : Fin 17 → TableIRow :=
  ![![1, 1, 0, 0, 0, 0], ![-1, 1, 1, 1, 0, 0], ![-1, 1, 1, 0, 0, 1], ![-1, 1, 0, 0, 1, 1], ![-1, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1], ![-1, 1, 2, 1, 2, 1], ![-1, 1, 1, 2, 1, 2], ![1, 1, 2, 2, 2, 2], ![2, 2, 1, 1, 1, 1]]

def data : GeneralizedDecompositionData (Fin 17) where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

def label : Fin 17 → Fin 7 :=
  ![0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 6]

def degree (x : Fin 7 → ℤ) : Fin 17 → ℤ := fun j => x (label j)

def offset : Fin 7 → ℤ := ![63, -51, 12, 63, -39, 87, 138]

def representative : Fin 7 → Fin 17 := ![0, 1, 5, 9, 13, 15, 16]

theorem signed_degree {x : Fin 7 → ℤ}
    (h : data.DegreeConstraints 0 (degree x)) (i : Fin 7) (hi : i ≠ 0) :
    LateSignedDegree (x i) (offset i) := by
  have hn : representative i ≠ 0 := by
    fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hd : degree x (representative i) = x i := by
    fin_cases i <;> rfl
  have hb : 3 * data.zValue (representative i) +
      60 * data.dT (representative i) = offset i := by
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hd] using h.degree_lower (representative i) hn
  · simpa only [hd, add_assoc, hb] using h.multiplicity_integral (representative i)
  · simpa only [hd, add_assoc, hb] using h.multiplicity_nonneg (representative i)

def tValue (x : Fin 7 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (-36 : ℚ) / (x 1) + (4 : ℚ) / (x 3) + (-98 : ℚ) / (x 4) + (81 : ℚ) / (x 5) + (72 : ℚ) / (x 6)

theorem tValue_eq (x : Fin 7 → ℤ) :
    data.weightedColumn (degree x) data.dT = tValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, tValue]; ring

def tInner (x : Fin 7 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (-4 : ℤ) * (x 1) + (4 : ℤ) * (x 3) + (-2 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (2 : ℤ) * (x 6)

theorem tInner_eq (x : Fin 7 → ℤ) :
    columnInner (degree x) data.dT = tInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, tInner]; ring

def zValue (x : Fin 7 → ℤ) : ℚ :=
  (1 : ℚ) / (x 0) + (36 : ℚ) / (x 1) + (64 : ℚ) / (x 2) + (98 : ℚ) / (x 4) + (81 : ℚ) / (x 5) + (72 : ℚ) / (x 6)

theorem zValue_eq (x : Fin 7 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 0) = zValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, zValue]; ring

def zInner (x : Fin 7 → ℤ) : ℤ :=
  (1 : ℤ) * (x 0) + (4 : ℤ) * (x 1) + (4 : ℤ) * (x 2) + (2 : ℤ) * (x 4) + (1 : ℤ) * (x 5) + (2 : ℤ) * (x 6)

theorem zInner_eq (x : Fin 7 → ℤ) :
    columnInner (degree x) (data.iDz 0) = zInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, zInner]; ring

def wValue (x : Fin 7 → ℤ) : ℚ :=
  (18 : ℚ) / (x 1) + (48 : ℚ) / (x 2) + (1 : ℚ) / (x 3) + (147 : ℚ) / (x 4) + (162 : ℚ) / (x 5) + (36 : ℚ) / (x 6)

theorem wValue_eq (x : Fin 7 → ℤ) :
    data.weightedColumn (degree x) (data.iDz 1) = wValue x := by
  simp [weightedColumn, GeneralizedDecompositionData.zValue, data, matrix, degree, label,
    Fin.sum_univ_succ, wValue]; ring

def wInner (x : Fin 7 → ℤ) : ℤ :=
  (2 : ℤ) * (x 1) + (3 : ℤ) * (x 2) + (1 : ℤ) * (x 3) + (3 : ℤ) * (x 4) + (2 : ℤ) * (x 5) + (1 : ℤ) * (x 6)

theorem wInner_eq (x : Fin 7 → ℤ) :
    columnInner (degree x) (data.iDz 1) = wInner x := by
  simp [columnInner, data, matrix, degree, label,
    Fin.sum_univ_succ, wInner]; ring

theorem constraints {x : Fin 7 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    x 0 = 1 ∧ tValue x = 0 ∧ zValue x = wValue x ∧ 0 < zValue x ∧
      tInner x = 0 ∧ zInner x = 0 ∧ wInner x = 0 := by
  refine ⟨hd.principal_degree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tValue_eq] using ho.zero_t
  · simpa only [zValue_eq, wValue_eq] using (ho.equal_z 1).symm
  · simpa only [zValue_eq] using ho.weighted_z_pos
  · simpa only [tInner_eq] using hd.orthogonal_t
  · simpa only [zInner_eq] using hd.orthogonal_z 0
  · simpa only [wInner_eq] using hd.orthogonal_z 1

end LateT

end Stellmacher.Recognition.LyonsU3Four
