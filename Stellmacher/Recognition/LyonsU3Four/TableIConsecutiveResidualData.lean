module

public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveFrame

/-!
# Residual row counts in Lyons's Case 5

After removing the four nonprincipal rows of Z₄, the other rows have period two.
This module fixes a finite catalogue for their proposed normalized row types,
with one count per Galois orbit. It specifies the remaining Gram equations and
records the four solutions corresponding to H, J, K, and L. Exhaustiveness of
the row catalogue and uniqueness of these four count vectors are separate
obligations; neither is asserted here.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 379,
Case 5(a)–(c). The J vector uses the corrected entry in `tableIMatrix`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData.ConsecutiveResidual
open scoped BigOperators

/-- Distinct period-two row candidates, with positive involution value. -/
def rows : Fin 33 → TableIRow := ![
  ![1, -1, 0, 1, 0, 1],
  ![1, -1, 1, 0, 1, 0],
  ![-1, -1, 1, 1, 1, 1],
  ![-2, 0, 0, 1, 0, 1],
  ![-2, 0, 1, 0, 1, 0],
  ![2, 0, 0, 1, 0, 1],
  ![2, 0, 1, 0, 1, 0],
  ![0, 0, 1, 1, 1, 1],
  ![-3, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0],
  ![-1, 1, 0, 1, 0, 1],
  ![-1, 1, 1, 0, 1, 0],
  ![3, 1, 0, 1, 0, 1],
  ![3, 1, 1, 0, 1, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1],
  ![-1, 1, 1, 2, 1, 2],
  ![-1, 1, 2, 1, 2, 1],
  ![1, 1, 2, 2, 2, 2],
  ![0, 2, 0, 1, 0, 1],
  ![0, 2, 1, 0, 1, 0],
  ![-2, 2, 1, 1, 1, 1],
  ![2, 2, 1, 1, 1, 1],
  ![0, 2, 1, 2, 1, 2],
  ![0, 2, 2, 1, 2, 1],
  ![-2, 2, 2, 2, 2, 2],
  ![2, 2, 2, 2, 2, 2],
  ![0, 2, 2, 3, 2, 3],
  ![0, 2, 3, 2, 3, 2],
  ![-1, 3, 2, 2, 2, 2],
  ![1, 3, 2, 3, 2, 3],
  ![1, 3, 3, 2, 3, 2],
  ![-1, 3, 3, 3, 3, 3]]

/-- Indices of the 23 Galois orbits in the residual row catalogue. -/
def orbit : Fin 33 → Fin 23 := ![0, 0, 1, 2, 2, 3, 3, 4, 5, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 13, 13, 14, 15, 16, 16, 17, 18, 19, 19, 20, 21, 21, 22]

/-- The remaining Gram matrix, after subtracting the four Z₄ rows. -/
def gramTarget : Fin 6 → Fin 6 → ℤ := ![
  ![12, -4, -4, -4, -4, -4],
  ![-4, 12, 8, 8, 8, 8],
  ![-4, 8, 10, 8, 10, 8],
  ![-4, 8, 8, 10, 8, 10],
  ![-4, 8, 10, 8, 10, 8],
  ![-4, 8, 8, 10, 8, 10]]

/-- One multiplicity for each orbit; every row within an orbit has that count. -/
def gram (n : Fin 23 → ℕ) (i j : Fin 6) : ℤ :=
  ∑ k : Fin 33, (n (orbit k) : ℤ) * rows k i * rows k j

/-- The finite arithmetic problem left by the Z₄ reduction. -/
structure CountConstraints (n : Fin 23 → ℕ) : Prop where
  gram_eq : ∀ i j, gram n i j = gramTarget i j
  principal_pos : 0 < n 6

/-- Full multiplicity, including the four distinguished Z₄ rows. -/
def multiplicity (n : Fin 23 → ℕ) (r : TableIRow) : ℕ := (∑ k : Fin 4, if TableICatalogue.z4 k.succ = r then 1 else 0) +
    ∑ k : Fin 33, if rows k = r then n (orbit k) else 0

/-- The residual orbit counts of H, J, K, L, respectively. -/
def counts : Fin 4 → Fin 23 → ℕ := ![
  ![0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]

def tableCase : Fin 4 → TableICase := ![.H, .J, .K, .L]

def tableVariant : (c : Fin 4) → (tableCase c).Variant :=
  Fin.cases () (Fin.cases () (Fin.cases () (Fin.cases () (fun i => Fin.elim0 i))))

/-- The four proposed count vectors do satisfy the remaining equations. -/
theorem counts_constraints (c : Fin 4) : CountConstraints (counts c) := by
  fin_cases c <;> constructor <;> decide

private def supportRows : Fin 37 → TableIRow :=
  Fin.append (fun k : Fin 4 => TableICatalogue.z4 k.succ) rows

private theorem canonical_mem_support (c : Fin 4) :
    ∀ j, ∃ k, supportRows k = tableIMatrix (tableCase c) (tableVariant c) j := by
  fin_cases c <;> decide

private theorem multiplicity_counts_on_support (c : Fin 4) :
    ∀ k, multiplicity (counts c) (supportRows k) =
      Fintype.card {j // tableIMatrix (tableCase c) (tableVariant c) j = supportRows k} := by
  fin_cases c <;> decide

/-- Each count vector reproduces the explicit canonical matrix, including
    every repeated row. -/
theorem multiplicity_counts (c : Fin 4) (r : TableIRow) :
    multiplicity (counts c) r =
      Fintype.card {j // tableIMatrix (tableCase c) (tableVariant c) j = r} := by
  classical
  by_cases hr : r ∈ Set.range supportRows
  · obtain ⟨k, rfl⟩ := hr
    exact multiplicity_counts_on_support c k
  · have hi (k : Fin 4) : TableICatalogue.z4 k.succ ≠ r := by
      intro hk
      exact hr ⟨Fin.castAdd 33 k, by simpa [supportRows] using hk⟩
    have hj (k : Fin 33) : rows k ≠ r := by
      intro hk
      exact hr ⟨Fin.natAdd 4 k, by simpa [supportRows] using hk⟩
    have he : IsEmpty {j // tableIMatrix (tableCase c) (tableVariant c) j = r} := by
      constructor
      intro j
      obtain ⟨k, hk⟩ := canonical_mem_support c j.val
      exact hr ⟨k, hk.trans j.property⟩
    simp [multiplicity, hi, hj]

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData.ConsecutiveResidual
