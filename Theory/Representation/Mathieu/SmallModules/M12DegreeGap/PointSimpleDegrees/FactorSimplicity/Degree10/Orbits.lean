module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10.Peak

/-!
# Degree-10 cyclic bases for the M₁₁ coset factor

The packed columns use exactly `Data.modelMatrix`, acting on column vectors.
All finite identities are checked by the Lean kernel. The low-rank operator
and the orbit bases are reproduced by `../source/discover.py` and `export.py`.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10
open Matrix

def transpose0 : Fin 10 → ℕ := fun j => (#[231, 1021, 1019, 533, 16, 936, 814, 102, 767, 772] : Array ℕ)[j.val]!

def transpose1 : Fin 10 → ℕ := fun j => (#[849, 210, 916, 30, 50, 870, 178, 784, 619, 409] : Array ℕ)[j.val]!

def transposes : Fin 2 → Fin 10 → ℕ := ![transpose0, transpose1]

theorem transposes_eq : ∀ s, matrix (m := 10) (transposes s) = (matrix (generators s)).transpose := by decide +kernel

def columns : Fin 10 → ℕ := fun j => (#[774, 598, 505, 783, 614, 879, 524, 641, 838, 226] : Array ℕ)[j.val]!

def columnsInverse : Fin 10 → ℕ := fun j => (#[894, 783, 494, 887, 315, 297, 257, 295, 57, 729] : Array ℕ)[j.val]!

def columnsParent : Fin 9 → Fin 10 := fun j => (#[0, 1, 1, 2, 3, 5, 6, 7, 7] : Array (Fin 10))[j.val]!

def columnsGenerator : Fin 9 → Fin 2 := fun j => (#[1, 0, 1, 1, 0, 1, 1, 0, 1] : Array (Fin 2))[j.val]!

private theorem columns_earlier : ∀ i, columnsParent i < i.succ := by decide +kernel

private theorem columns_step : ∀ i, act (generators (columnsGenerator i)) (columns (columnsParent i)) = columns i.succ := by decide +kernel

private theorem columns_inverse : product columns columnsInverse = identity 10 := by decide +kernel

theorem columns_top (U : Submodule (ZMod 2) (Fin 10 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s))) (hseed : vector 774 ∈ U) : U = ⊤ := by
  exact eq_top_of_column_orbit U generators hA columns columnsInverse
    columnsParent columnsGenerator columns_earlier columns_step columns_inverse hseed

def rows : Fin 10 → ℕ := fun j => (#[260, 511, 660, 137, 303, 95, 931, 7, 225, 23] : Array ℕ)[j.val]!

def rowsInverse : Fin 10 → ℕ := fun j => (#[186, 343, 365, 724, 640, 808, 244, 614, 364, 399] : Array ℕ)[j.val]!

def rowsParent : Fin 9 → Fin 10 := fun j => (#[0, 1, 2, 2, 3, 4, 6, 7, 7] : Array (Fin 10))[j.val]!

def rowsGenerator : Fin 9 → Fin 2 := fun j => (#[1, 1, 0, 1, 1, 0, 1, 0, 1] : Array (Fin 2))[j.val]!

private theorem rows_earlier : ∀ i, rowsParent i < i.succ := by decide +kernel

private theorem rows_step : ∀ i, act (transposes (rowsGenerator i)) (rows (rowsParent i)) = rows i.succ := by decide +kernel

private theorem rows_inverse : product rows rowsInverse = identity 10 := by decide +kernel

theorem simple_of_detects (U : Submodule (ZMod 2) (Fin 10 → ZMod 2))
    (hA : ∀ s, Preserves U (matrix (generators s)))
    (hbase : ∀ x ∈ U, vector 260 ⬝ᵥ x ≠ 0 → U = ⊤) : U = ⊥ ∨ U = ⊤ := by
  exact simple_of_row_orbit U generators transposes hA transposes_eq rows rowsInverse
    rowsParent rowsGenerator rows_earlier rows_step rows_inverse hbase

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10
