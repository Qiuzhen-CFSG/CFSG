module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion.Certificate
public import Theory.ElementaryAbelian.Basic

/-!
# The two elementary subgroups in an enumerated native M23 Sylow group

Two sixteen-element sublists of the certified Sylow permutations are closed
under multiplication, with product given by bitwise XOR. The other eight
involutions have only twelve commuting elements whose squares are one.
These finite statements support the exhaustive E16 classification in the
parent module. All numerical identities are checked by the Lean kernel.

Source: Aschbacher–Smith, H.14.2(1), printed p.397. The underlying native
permutations and membership certificates come from `Involutions.Fusion`.
-/

@[expose] public section

open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.ElementarySylow
open FusionCertificate
set_option maxRecDepth 100000

set_option Elab.async false

def candidateIndex (b : Fin 2) (i : Fin 16) : Fin 128 :=
  if b = 0 then
    (#[0,3,5,6,48,51,53,54,88,91,93,94,104,107,109,110] : Array (Fin 128))[i.val]'(by exact i.isLt)
  else
    (#[0,8,17,25,34,42,51,59,68,76,85,93,102,110,119,127] : Array (Fin 128))[i.val]'(by exact i.isLt)

def productIndex (_ : Fin 2) (i j : Fin 16) : Fin 16 := i ^^^ j
def exceptionalIndex : Fin 8 → Fin 128 := ![1, 7, 16, 35, 50, 52, 75, 120]
def commutingIndex : Fin 8 → Fin 12 → Fin 128 := ![![0, 1, 5, 7, 16, 17, 34, 35, 50, 51, 52, 54], ![0, 1, 5, 7, 50, 51, 52, 54, 75, 76, 120, 127], ![0, 1, 16, 17, 34, 35, 50, 51, 75, 88, 107, 120], ![0, 1, 16, 17, 34, 35, 50, 51, 75, 88, 107, 120], ![0, 1, 5, 7, 16, 17, 34, 35, 50, 51, 52, 54], ![0, 1, 5, 7, 50, 51, 52, 54, 75, 76, 120, 127], ![0, 7, 16, 35, 51, 52, 75, 76, 88, 107, 120, 127], ![0, 7, 16, 35, 51, 52, 75, 76, 88, 107, 120, 127]]

theorem candidate_initial (b : Fin 2) : candidateIndex b 0 = 0 := by
  fin_cases b <;> rfl

theorem candidate_injective : ∀ b, Function.Injective (candidateIndex b) := by
  decide +kernel

private theorem product_points_0_0 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 0) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 0 j)) x := by decide +kernel

private theorem product_points_0_1 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 1) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 1 j)) x := by decide +kernel

private theorem product_points_0_2 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 2) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 2 j)) x := by decide +kernel

private theorem product_points_0_3 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 3) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 3 j)) x := by decide +kernel

private theorem product_points_0_4 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 4) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 4 j)) x := by decide +kernel

private theorem product_points_0_5 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 5) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 5 j)) x := by decide +kernel

private theorem product_points_0_6 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 6) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 6 j)) x := by decide +kernel

private theorem product_points_0_7 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 7) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 7 j)) x := by decide +kernel

private theorem product_points_0_8 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 8) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 8 j)) x := by decide +kernel

private theorem product_points_0_9 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 9) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 9 j)) x := by decide +kernel

private theorem product_points_0_10 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 10) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 10 j)) x := by decide +kernel

private theorem product_points_0_11 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 11) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 11 j)) x := by decide +kernel

private theorem product_points_0_12 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 12) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 12 j)) x := by decide +kernel

private theorem product_points_0_13 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 13) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 13 j)) x := by decide +kernel

private theorem product_points_0_14 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 14) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 14 j)) x := by decide +kernel

private theorem product_points_0_15 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 0 15) (pointTable (candidateIndex 0 j) x) =
      pointTable (candidateIndex 0 (productIndex 0 15 j)) x := by decide +kernel

private theorem product_points_1_0 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 0) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 0 j)) x := by decide +kernel

private theorem product_points_1_1 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 1) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 1 j)) x := by decide +kernel

private theorem product_points_1_2 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 2) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 2 j)) x := by decide +kernel

private theorem product_points_1_3 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 3) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 3 j)) x := by decide +kernel

private theorem product_points_1_4 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 4) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 4 j)) x := by decide +kernel

private theorem product_points_1_5 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 5) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 5 j)) x := by decide +kernel

private theorem product_points_1_6 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 6) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 6 j)) x := by decide +kernel

private theorem product_points_1_7 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 7) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 7 j)) x := by decide +kernel

private theorem product_points_1_8 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 8) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 8 j)) x := by decide +kernel

private theorem product_points_1_9 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 9) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 9 j)) x := by decide +kernel

private theorem product_points_1_10 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 10) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 10 j)) x := by decide +kernel

private theorem product_points_1_11 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 11) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 11 j)) x := by decide +kernel

private theorem product_points_1_12 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 12) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 12 j)) x := by decide +kernel

private theorem product_points_1_13 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 13) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 13 j)) x := by decide +kernel

private theorem product_points_1_14 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 14) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 14 j)) x := by decide +kernel

private theorem product_points_1_15 : ∀ (j : Fin 16) (x : Fin 23),
    pointTable (candidateIndex 1 15) (pointTable (candidateIndex 1 j) x) =
      pointTable (candidateIndex 1 (productIndex 1 15 j)) x := by decide +kernel

private theorem product_points (b : Fin 2) (i j : Fin 16) (x : Fin 23) :
    pointTable (candidateIndex b i) (pointTable (candidateIndex b j) x) =
      pointTable (candidateIndex b (productIndex b i j)) x := by
  fin_cases b <;> fin_cases i
  · exact product_points_0_0 j x
  · exact product_points_0_1 j x
  · exact product_points_0_2 j x
  · exact product_points_0_3 j x
  · exact product_points_0_4 j x
  · exact product_points_0_5 j x
  · exact product_points_0_6 j x
  · exact product_points_0_7 j x
  · exact product_points_0_8 j x
  · exact product_points_0_9 j x
  · exact product_points_0_10 j x
  · exact product_points_0_11 j x
  · exact product_points_0_12 j x
  · exact product_points_0_13 j x
  · exact product_points_0_14 j x
  · exact product_points_0_15 j x
  · exact product_points_1_0 j x
  · exact product_points_1_1 j x
  · exact product_points_1_2 j x
  · exact product_points_1_3 j x
  · exact product_points_1_4 j x
  · exact product_points_1_5 j x
  · exact product_points_1_6 j x
  · exact product_points_1_7 j x
  · exact product_points_1_8 j x
  · exact product_points_1_9 j x
  · exact product_points_1_10 j x
  · exact product_points_1_11 j x
  · exact product_points_1_12 j x
  · exact product_points_1_13 j x
  · exact product_points_1_14 j x
  · exact product_points_1_15 j x

theorem product_correct (b : Fin 2) (i j : Fin 16) :
    perm (candidateIndex b i) * perm (candidateIndex b j) =
      perm (candidateIndex b (productIndex b i j)) :=
  Equiv.ext (product_points b i j)

theorem product_symmetric : ∀ (b : Fin 2) (i j : Fin 16),
    productIndex b i j = productIndex b j i := by decide +kernel

theorem product_diagonal : ∀ (b : Fin 2) (i : Fin 16),
    productIndex b i i = 0 := by decide +kernel

theorem candidate_sq (b : Fin 2) (i : Fin 16) :
    perm (candidateIndex b i) * perm (candidateIndex b i) = 1 := by
  rw [product_correct, product_diagonal, candidate_initial, initial]

end Sporadic.Mathieu.M23Geometry.ElementarySylow
