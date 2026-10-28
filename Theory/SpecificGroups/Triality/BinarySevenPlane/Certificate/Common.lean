module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Coefficients
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.Data

/-!
# Sparse matrix certificates over the cubic coefficient ring

Column lists reduce multiplication by a root curve to its nonzero entries.
The certificate matrices retain all twenty-eight Geck coordinates. Their
connection to the actual group uses the canonical root-curve comparison;
coefficient equalities here do not by themselves assert group membership.
Source: the explicit eleven-factor binary triality construction, ATLAS p.89.
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane.Certificate
open Coefficients PositiveCoordinates.SumExchangeData
open scoped BigOperators

def curve (r : Fin 24) (t : Scalar) : Matrix (Fin 28) (Fin 28) Scalar :=
  Matrix.reindexRingEquiv Scalar finSumFinEquiv (matrixCurve r t)

def columnEntry (l : List (Fin 28 × Scalar)) (i : Fin 28) : Scalar :=
  (l.map fun p => if i = p.1 then p.2 else 0).sum

lemma sum_mul_columnEntry (r : Fin 28 → Scalar) (l : List (Fin 28 × Scalar)) :
    (∑ i, r i * columnEntry l i) = (l.map fun p => r p.1 * p.2).sum := by
  induction l with
  | nil => simp [columnEntry]
  | cons p l ih =>
    simp only [columnEntry, List.map_cons, List.sum_cons, mul_add,
      Finset.sum_add_distrib] at *
    rw [ih]
    simp

lemma mul_of_columns (A B C : Matrix (Fin 28) (Fin 28) Scalar)
    (cols : Fin 28 → List (Fin 28 × Scalar))
    (hb : ∀ i j, B i j = columnEntry (cols j) i)
    (hc : ∀ i j, ((cols j).map (fun p => A i p.1 * p.2)).sum.val = (C i j).val) :
    A * B = C := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [hb]
  rw [sum_mul_columnEntry]
  exact congrArg Scalar.mk (hc i j)

end Triality.Standard.BinarySevenPlane.Certificate
