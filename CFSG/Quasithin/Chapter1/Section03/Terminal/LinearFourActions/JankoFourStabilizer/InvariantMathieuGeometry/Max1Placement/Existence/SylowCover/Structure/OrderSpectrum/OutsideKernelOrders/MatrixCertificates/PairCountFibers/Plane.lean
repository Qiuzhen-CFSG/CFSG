module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.Coordinates
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.Commute

/-!
# Pair-rank identities for binary planes in the literal candidates

Swapping two commuting generators or replacing `(x,y)` by `(x,xy)` for an
involution x preserves the pair rank. Identity and equal pairs have rank zero.
Checked PC collection proves the involution premise for every enumerated
point of rows 5–8. Literal word comparisons embed rows 5 and 7 into rows 6
and 8; both coordinates of each pair are transported.
Source context: Aschbacher–Smith A.3.12, printed pp.47–48;
Kleidman–Wilson (1988), pp.484–510.
-/

public section

open Janko4 Janko4.LocalStructure.SylowNormalEights
open Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB

private theorem matrix_neg_eq (a : BinaryMatrix) : -a = a := by
  ext i j
  exact CharTwo.neg_eq _

private theorem matrix_sub_eq_add (a b : BinaryMatrix) : a - b = a + b := by
  rw [sub_eq_add_neg, matrix_neg_eq]

private theorem matrix_add_self (a : BinaryMatrix) : a + a = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

theorem pairRank_one_left (y : Model) : pairRank 1 y = 0 := by
  simp [pairRank]

theorem pairRank_one_right (x : Model) : pairRank x 1 = 0 := by
  simp [pairRank]

theorem pairRank_swap (x y : Model) (hxy : x * y = y * x) :
    pairRank x y = pairRank y x := by
  have hc : Commute (toMatrix x) (toMatrix y) := by
    change toMatrix x * toMatrix y = toMatrix y * toMatrix x
    simpa only [map_mul] using congrArg toMatrix hxy
  unfold pairRank
  apply congrArg (fun a : BinaryMatrix => a.rank)
  generalize toMatrix x = a at hc ⊢
  generalize toMatrix y = b at hc ⊢
  change a * b = b * a at hc
  simp only [mul_sub, sub_mul, mul_one, one_mul, hc]
  abel

/-- The displacement square of a binary involution vanishes, so dependent
pairs contribute no rank-16 elements. -/
theorem pairRank_self (x : Model) (hx : x * x = 1) : pairRank x x = 0 := by
  have hm : toMatrix x * toMatrix x = 1 := by
    rw [← map_mul, hx, map_one]
  have he : (toMatrix x - 1) * (toMatrix x - 1) = 0 := by
    rw [matrix_sub_eq_add, add_mul, mul_add, mul_add, hm, mul_one, one_mul, one_mul]
    calc
      1 + toMatrix x + (toMatrix x + 1) =
          (1 + 1) + (toMatrix x + toMatrix x) := by ac_rfl
      _ = 0 := by rw [matrix_add_self, matrix_add_self, add_zero]
  rw [pairRank, he, Matrix.rank_zero]

/-- Replacing a plane basis `(x,y)` by `(x,xy)` preserves the actual product
of binary displacements, not just its rank. -/
theorem displacement_product_shear (x y : Model) (hx : x * x = 1) :
    (toMatrix x - 1) * (toMatrix (x * y) - 1) =
      (toMatrix x - 1) * (toMatrix y - 1) := by
  have hm : toMatrix x * toMatrix x = 1 := by
    rw [← map_mul, hx, map_one]
  rw [map_mul]
  generalize toMatrix x = a at hm ⊢
  generalize toMatrix y = b
  rw [matrix_sub_eq_add a 1, matrix_sub_eq_add (a * b) 1, matrix_sub_eq_add b 1]
  rw [add_mul, mul_add, one_mul, mul_one, ← mul_assoc, hm, one_mul]
  rw [add_mul, mul_add, one_mul, mul_one]
  abel

theorem pairRank_shear (x y : Model) (hx : x * x = 1) :
    pairRank x (x * y) = pairRank x y :=
  congrArg Matrix.rank (displacement_product_shear x y hx)

/-- The actual coordinate-zero word is the identity in every candidate. -/
theorem point_zero (i : Fin 9) : point i ⟨0, by
    have h : ∀ i : Fin 9, 0 < candidateOrder i := by decide +kernel
    exact h i⟩ = 1 := by
  have h : ∀ i : Fin 9, selectWords (candidateWords i) 0 = [] := by decide +kernel
  simp only [point_eq_word, h, List.map_nil, List.prod_nil]

/-- Literal inclusion of row 5 into row 6, preserving the original word order. -/
theorem point_five_six (n : Fin 64) :
    point (5 : Fin 9) n = point (6 : Fin 9) ⟨2 * n.val, by change 2 * n.val < 128; omega⟩ := by
  apply congrArg realization
  apply congrArg wordValue
  exact (by decide +kernel : ∀ n : Fin 64,
    selectWords (candidateWords 5) n.val =
      selectWords (candidateWords 6) (2 * n.val)) n

/-- Literal inclusion of row 7 into row 8, preserving the original word order. -/
theorem point_seven_eight (n : Fin 128) :
    point (7 : Fin 9) n = point (8 : Fin 9) ⟨2 * n.val, by change 2 * n.val < 256; omega⟩ := by
  apply congrArg realization
  apply congrArg wordValue
  exact (by decide +kernel : ∀ n : Fin 128,
    selectWords (candidateWords 7) n.val =
      selectWords (candidateWords 8) (2 * n.val)) n

/-- Pair ranks restrict along the actual inclusion, with both coordinates transported. -/
theorem pairRank_five_six (a b : Fin 64) :
    pairRank (point (5 : Fin 9) a) (point (5 : Fin 9) b) =
      pairRank (point (6 : Fin 9) ⟨2 * a.val, by change 2 * a.val < 128; omega⟩)
        (point (6 : Fin 9) ⟨2 * b.val, by change 2 * b.val < 128; omega⟩) := by
  rw [point_five_six, point_five_six]

theorem pairRank_seven_eight (a b : Fin 128) :
    pairRank (point (7 : Fin 9) a) (point (7 : Fin 9) b) =
      pairRank (point (8 : Fin 9) ⟨2 * a.val, by change 2 * a.val < 256; omega⟩)
        (point (8 : Fin 9) ⟨2 * b.val, by change 2 * b.val < 256; omega⟩) := by
  rw [point_seven_eight, point_seven_eight]

/-- Every enumerated element in the last four rows has square one, checked
in the presentation and transported by its actual matrix realization. -/
theorem point_square (i : Fin 9) (hi : 5 ≤ i.val) (n : Fin (candidateOrder i)) :
    point i n * point i n = 1 := by
  have h : ∀ (i : Fin 9), 5 ≤ i.val → ∀ n : Fin (candidateOrder i),
      collect 128 (selectWords (candidateWords i) n.val ++
        selectWords (candidateWords i) n.val) = [] := by
    intro i
    fin_cases i <;> decide +kernel
  change realization (abstractPoint i n) * realization (abstractPoint i n) = 1
  rw [← map_mul]
  have he : abstractPoint i n * abstractPoint i n = 1 := by
    simpa only [abstractPoint, wordValue_append, wordValue_nil] using
      wordValue_eq_of_collect 128 _ _ (h i hi n)
  rw [he, map_one]

/-- The dependent nonidentity pairs contribute zero in the literal enumeration. -/
theorem pairRank_point_self (i : Fin 9) (hi : 5 ≤ i.val) (n : Fin (candidateOrder i)) :
    pairRank (point i n) (point i n) = 0 :=
  pairRank_self _ (point_square i hi n)

/-- A change of basis in the actual candidate plane preserves the pair rank. -/
theorem pairRank_point_shear (i : Fin 9) (hi : 5 ≤ i.val)
    (n m : Fin (candidateOrder i)) :
    pairRank (point i n) (point i n * point i m) = pairRank (point i n) (point i m) :=
  pairRank_shear _ _ (point_square i hi n)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
