module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity

/-!
# Integral rows for the sparse difference cases of Table I

Rows are oriented by positive involution value. We list representatives of the
51 rotation orbits satisfying the strict contribution inequality, congruence,
and sparse unit difference conditions. The list retains the distinction between
row support and row multiplicity; it does not assert classification of matrices.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Cases 6–8.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators

namespace SparseOppositeRows

/-- The Galois rotation of a six-entry row. -/
def rotate (r : TableIRow) : TableIRow :=
  ![r 0, r 1, r 5, r 2, r 3, r 4]

/-- A rotation indexed by the cyclic group of order four. -/
def rotation (r : TableIRow) (k : Fin 4) : TableIRow :=
  ![r, rotate r, rotate (rotate r), rotate (rotate (rotate r))] k

/-- The integral contribution numerator as a polynomial in row entries. -/
def contribution (r : TableIRow) : ℤ :=
  4 * r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 + r 4 ^ 2 + r 5 ^ 2 +
  3 * ((r 1 - r 2)^2 + (r 1 - r 3)^2 + (r 1 - r 4)^2 +
    (r 1 - r 5)^2 + (r 2 - r 3)^2 + (r 2 - r 4)^2 +
    (r 2 - r 5)^2 + (r 3 - r 4)^2 + (r 3 - r 5)^2 + (r 4 - r 5)^2)

/-- The involution value of a row. -/
def value (r : TableIRow) : ℤ := r 1 + r 2 + r 3 + r 4 + r 5

/-- The four adjacent differences, starting at the first rotating column. -/
def difference (r : TableIRow) : Fin 4 → ℤ :=
  ![r 2 - r 3, r 3 - r 4, r 4 - r 5, r 5 - r 2]

/-- The local integer restrictions in the sparse cases. -/
def Admissible (r : TableIRow) : Prop :=
  0 < value r ∧ contribution r < 64 ∧ Int.ModEq 4 (r 0) (value r) ∧
  (∀ i, -1 ≤ difference r i ∧ difference r i ≤ 1) ∧
  ∀ i, difference r i * difference r (![1, 2, 3, 0] i) ≠ 1

instance (r : TableIRow) : Decidable (Admissible r) := by
  unfold Admissible
  infer_instance

/-- Representatives of all 51 sparse integral row orbits. -/
def representative : Fin 51 → TableIRow := ![
  ![-3, 0, 0, 0, 0, 1],
  ![-3, 1, 0, 0, 0, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![-2, 0, 0, 0, 1, 1],
  ![-2, 0, 0, 1, 0, 1],
  ![-2, 1, 0, 0, 0, 1],
  ![-2, 1, 1, 1, 1, 2],
  ![-2, 2, 1, 1, 1, 1],
  ![-2, 2, 2, 2, 2, 2],
  ![-1, -1, 1, 1, 1, 1],
  ![-1, 0, 0, 1, 1, 1],
  ![-1, 1, 0, 0, 1, 1],
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 1, 2, 2],
  ![-1, 1, 1, 2, 1, 2],
  ![-1, 2, 0, 0, 0, 1],
  ![-1, 2, 1, 1, 1, 2],
  ![-1, 2, 2, 2, 2, 3],
  ![-1, 3, 2, 2, 2, 2],
  ![-1, 3, 3, 3, 3, 3],
  ![0, 0, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1, 1],
  ![0, 1, 1, 2, 2, 2],
  ![0, 2, 0, 0, 1, 1],
  ![0, 2, 0, 1, 0, 1],
  ![0, 2, 1, 1, 2, 2],
  ![0, 2, 1, 2, 1, 2],
  ![0, 2, 2, 2, 3, 3],
  ![0, 2, 2, 3, 2, 3],
  ![0, 3, 2, 2, 2, 3],
  ![1, -1, 0, 0, 1, 1],
  ![1, -1, 0, 1, 0, 1],
  ![1, 0, 0, 0, 0, 1],
  ![1, 0, 1, 1, 1, 2],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 2, 0, 1, 1, 1],
  ![1, 2, 1, 2, 2, 2],
  ![1, 2, 2, 3, 3, 3],
  ![1, 3, 2, 2, 3, 3],
  ![1, 3, 2, 3, 2, 3],
  ![2, 0, 0, 0, 1, 1],
  ![2, 0, 0, 1, 0, 1],
  ![2, 1, 0, 0, 0, 1],
  ![2, 1, 1, 1, 1, 2],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 2, 2, 2, 2],
  ![3, 0, 0, 1, 1, 1],
  ![3, 1, 0, 0, 1, 1],
  ![3, 1, 0, 1, 0, 1]]

/-- Number of distinct rows in each rotation orbit. -/
def orbitSize : Fin 51 → ℕ :=
  ![4, 1, 1, 4, 2, 4, 4, 1, 1, 1, 4, 4, 2, 4, 2, 4, 4, 4, 1, 1, 1, 4, 4, 4, 2, 4, 2, 4, 2, 4, 4, 2, 4, 4, 1, 1, 1, 4, 4, 4, 4, 2, 4, 2, 4, 4, 1, 1, 4, 4, 2]

/-- The set of rows in a representative's rotation orbit. -/
def orbit (p : Fin 51) : Finset TableIRow :=
  Finset.univ.image (rotation (representative p))

/-- Every listed row meets the local numerical restrictions. -/
theorem representative_admissible (p : Fin 51) (k : Fin 4) :
    Admissible (rotation (representative p) k) := by
  revert p k
  decide

/-- Orbit sizes count distinct rows, rather than four rotations with repetitions. -/
theorem orbit_card (p : Fin 51) : (orbit p).card = orbitSize p := by
  revert p
  decide


/-- The eight independent Gram entries after rotation symmetry. -/
def gramPairs : Fin 8 → Fin 6 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (2, 3), (2, 4)]

/-- Contribution of a complete orbit, once per distinct row. -/
def moment (p : Fin 51) (i : Fin 8) : ℤ :=
  ∑ r ∈ orbit p, r (gramPairs i).1 * r (gramPairs i).2

/-- Explicit integral coefficients of the eight orbit Gram equations. -/
def gramCoefficient : Fin 8 → Fin 51 → ℤ := ![
  ![36, 9, 9, 16, 8, 16, 16, 4, 4, 1, 4, 4, 2, 4, 2, 4, 4, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 4, 1, 1, 1, 4, 4, 4, 4, 2, 16, 8, 16, 16, 4, 4, 36, 36, 18],
  ![0, -3, -3, 0, 0, -8, -8, -4, -4, 1, 0, -4, -2, -4, -2, -8, -8, -8, -3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, -2, 0, 0, 1, 1, 1, 8, 8, 8, 12, 6, 0, 0, 8, 8, 4, 4, 0, 12, 6],
  ![-3, 0, -3, -4, -2, -2, -10, -2, -4, -1, -3, -2, -1, -6, -3, -1, -5, -9, -2, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 5, 0, 1, 2, 3, 7, 11, 10, 5, 4, 2, 2, 10, 2, 4, 9, 6, 3],
  ![0, 1, 1, 0, 0, 4, 4, 4, 4, 1, 0, 4, 2, 4, 2, 16, 16, 16, 9, 9, 0, 4, 4, 16, 8, 16, 8, 16, 8, 36, 4, 2, 0, 0, 1, 1, 1, 16, 16, 16, 36, 18, 0, 0, 4, 4, 4, 4, 0, 4, 2],
  ![0, 0, 1, 0, 0, 1, 5, 2, 4, -1, 0, 2, 1, 6, 3, 2, 10, 18, 6, 9, 0, 3, 7, 4, 2, 12, 6, 20, 10, 27, -2, -1, 0, 0, 0, 1, 2, 6, 14, 22, 30, 15, 0, 0, 1, 5, 2, 4, 0, 2, 1],
  ![1, 0, 1, 2, 1, 1, 7, 1, 4, 1, 3, 2, 1, 10, 5, 1, 7, 21, 4, 9, 1, 3, 13, 2, 1, 10, 5, 26, 13, 21, 2, 1, 1, 7, 0, 1, 4, 3, 13, 31, 26, 13, 2, 1, 1, 7, 1, 4, 3, 2, 1],
  ![0, 0, 1, 1, 0, 0, 6, 1, 4, 1, 2, 1, 0, 9, 4, 0, 6, 20, 4, 9, 1, 2, 12, 1, 0, 9, 4, 25, 12, 20, 1, 0, 0, 6, 0, 1, 4, 2, 12, 30, 25, 12, 1, 0, 0, 6, 1, 4, 2, 1, 0],
  ![0, 0, 1, 0, 1, 0, 6, 1, 4, 1, 2, 0, 1, 8, 5, 0, 6, 20, 4, 9, 1, 2, 12, 0, 1, 8, 5, 24, 13, 20, 0, 1, 0, 6, 0, 1, 4, 2, 12, 30, 24, 13, 0, 1, 0, 6, 1, 4, 2, 0, 1]]

/-- The target Gram entries are exactly (3.2). -/
def gramValue : Fin 8 → ℤ := ![16, 0, 0, 16, 12, 16, 12, 12]

/-- Evaluation of each orbit's Gram contribution. -/
theorem moment_eq (p : Fin 51) (i : Fin 8) :
    moment p i = gramCoefficient i p := by
  revert p i
  decide

/-- Orbits containing an opposite sparse difference row. -/
def oppositeOrbits : Finset (Fin 51) := {3, 11, 13, 23, 25, 27, 30, 40, 42, 49}

/-- The opposite mask is computed from the actual difference vectors. -/
theorem opposite_iff (p : Fin 51) : p ∈ oppositeOrbits ↔
    ∃ k, difference (rotation (representative p) k) = ![1, 0, -1, 0] ∨
      difference (rotation (representative p) k) = ![-1, 0, 1, 0] := by
  revert p
  decide

set_option maxRecDepth 2048 in
/-- Distinct representatives have disjoint row orbits. -/
theorem orbit_disjoint (p q : Fin 51) (h : p ≠ q) :
    Disjoint (orbit p) (orbit q) := by
  revert p q
  decide +kernel

/-- The four possible multiplicity vectors, ordered S, T, U, V. -/
def modelCounts : Fin 4 → Fin 51 → ℕ := ![
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The model labels refer to the actual Table I cases. -/
def modelCase : Fin 4 → TableICase := ![.S, .T, .U, .V]

def modelVariant : (v : Fin 4) → (modelCase v).Variant
  | 0 => ()
  | 1 => ()
  | 2 => ()
  | 3 => ()

/-- Explicit model multiplicities agree with the printed matrices, including
all duplicate rows. -/
theorem modelCounts_eq (v : Fin 4) (p : Fin 51) :
    modelCounts v p = Fintype.card {j //
      tableIMatrix (modelCase v) (modelVariant v) j = representative p} := by
  revert v p
  decide

set_option maxRecDepth 2048 in
/-- Every row of the four actual matrices belongs to the row catalogue. -/
theorem model_supported (v : Fin 4)
    (j : Fin (tableIRowCount (modelCase v))) :
    ∃ p, tableIMatrix (modelCase v) (modelVariant v) j ∈ orbit p := by
  revert v j
  decide

/-- A rotation is an actual member of its representative's orbit. -/
theorem rotation_mem_orbit (p : Fin 51) (k : Fin 4) :
    rotation (representative p) k ∈ orbit p := by
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- The catalogue orbits are closed under one further Galois rotation. -/
theorem rotate_mem_orbit (p : Fin 51) (k : Fin 4) :
    rotate (rotation (representative p) k) ∈ orbit p := by
  revert p k
  decide

/-- Model row counts are constant throughout each rotation orbit. -/
theorem modelCounts_rotation_eq (v : Fin 4) (p : Fin 51) (k : Fin 4) :
    modelCounts v p = Fintype.card {j //
      tableIMatrix (modelCase v) (modelVariant v) j =
        rotation (representative p) k} := by
  revert v p k
  decide +kernel

/-- The finite integer multiplicity problem. Its variables count each distinct
row in a rotation orbit, not the total number of rows in that orbit. -/
structure MultiplicityConstraints (m : Fin 51 → ℕ) : Prop where
  gram : ∀ i, ∑ p, (m p : ℤ) * gramCoefficient i p = gramValue i
  principal : 1 ≤ m 34
  opposite : 1 ≤ ∑ p ∈ oppositeOrbits, m p

end SparseOppositeRows
end Stellmacher.Recognition.LyonsU3Four
