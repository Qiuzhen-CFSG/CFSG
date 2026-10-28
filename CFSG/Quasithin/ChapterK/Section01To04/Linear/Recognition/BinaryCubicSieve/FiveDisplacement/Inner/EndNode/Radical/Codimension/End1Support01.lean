module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.Commuting
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Nine cosets for end 1 and support `{0, 1}`

Each root action follows from the local highest-vector relations, with
finite matrix identities checked by kernel reduction. The nine extracting
operators kill the common fixed space because their first applied root
lies in the marked radical. Their triangular action proves independence
of nine cosets, and hence fixed codimension at least nine.

Four of the chosen vectors are root differences of permutation translates.
Commuting differences are reordered only to evaluate the extraction; its
first applied radical difference is retained in the quotient factorization.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.7 step 1, pp.25–26; Aschbacher–Smith K.3.2, pp.454–455.
-/

public section
open Representation Representation.BinaryOffender
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension.End1Support01
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) SL5TenDimensional.Group V} {v : V}

private def permutationElement (p : Equiv.Perm (Fin 5)) : SL5TenDimensional.Group :=
  ⟨p.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp] <;> decide⟩

private def w0 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 2, 3, 4, 1], ![0, 4, 1, 2, 3], by decide +kernel, by decide +kernel⟩

private def w1 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 2, 1, 3, 4], ![0, 2, 1, 3, 4], by decide +kernel, by decide +kernel⟩

private def w2 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide +kernel, by decide +kernel⟩

private def w3 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], by decide +kernel, by decide +kernel⟩

private def w4 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 0, 4, 1], ![2, 4, 0, 1, 3], by decide +kernel, by decide +kernel⟩

private def w5 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 1, 0, 3, 4], ![2, 1, 0, 3, 4], by decide +kernel, by decide +kernel⟩

private def w6 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide +kernel, by decide +kernel⟩

private def w7 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 1, 3, 4, 0], ![4, 1, 0, 2, 3], by decide +kernel, by decide +kernel⟩

private def w8 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 1, 3, 0, 4], ![3, 1, 0, 2, 4], by decide +kernel, by decide +kernel⟩

private def w9 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 0, 3, 1, 4], ![1, 3, 0, 2, 4], by decide +kernel, by decide +kernel⟩

private def w10 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 0, 3, 4, 1], ![1, 4, 0, 2, 3], by decide +kernel, by decide +kernel⟩

private def w11 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide +kernel, by decide +kernel⟩

private def w12 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide +kernel, by decide +kernel⟩

private def w13 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 1, 0, 4], ![3, 2, 0, 1, 4], by decide +kernel, by decide +kernel⟩

private def w14 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 2, 3, 4], ![1, 0, 2, 3, 4], by decide +kernel, by decide +kernel⟩

private def w15 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide +kernel, by decide +kernel⟩

private def w16 : SL5TenDimensional.Group :=
  permutationElement ⟨![2, 3, 4, 1, 0], ![4, 3, 0, 1, 2], by decide +kernel, by decide +kernel⟩

private def w17 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 2, 3, 1, 4], ![0, 3, 1, 2, 4], by decide +kernel, by decide +kernel⟩

private theorem exchange0
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 2 4) (difference σ (rootElement 2 0) x) =
      difference σ (rootElement 2 0) (difference σ (rootElement 2 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange1
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 2 4) (difference σ (rootElement 1 4) x) =
      difference σ (rootElement 1 4) (difference σ (rootElement 2 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange2
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 0 4) (difference σ (rootElement 2 4) x) =
      difference σ (rootElement 2 4) (difference σ (rootElement 0 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange3
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 0 1) (difference σ (rootElement 0 4) x) =
      difference σ (rootElement 0 4) (difference σ (rootElement 0 1) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange4
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 0 1) (difference σ (rootElement 2 4) x) =
      difference σ (rootElement 2 4) (difference σ (rootElement 0 1) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange5
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 3) (difference σ (rootElement 2 4) x) =
      difference σ (rootElement 2 4) (difference σ (rootElement 1 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange6
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 3) (difference σ (rootElement 4 3) x) =
      difference σ (rootElement 4 3) (difference σ (rootElement 1 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange7
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 2 4) (difference σ (rootElement 0 3) x) =
      difference σ (rootElement 0 3) (difference σ (rootElement 2 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange8
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 2) (difference σ (rootElement 1 3) x) =
      difference σ (rootElement 1 3) (difference σ (rootElement 1 2) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange9
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 2) (difference σ (rootElement 0 3) x) =
      difference σ (rootElement 0 3) (difference σ (rootElement 1 2) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange10
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 3) (difference σ (rootElement 0 3) x) =
      difference σ (rootElement 0 3) (difference σ (rootElement 1 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange11
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 2 3) (difference σ (rootElement 2 4) x) =
      difference σ (rootElement 2 4) (difference σ (rootElement 2 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange12
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 3) (difference σ (rootElement 2 3) x) =
      difference σ (rootElement 2 3) (difference σ (rootElement 1 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange13
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 2 3) (difference σ (rootElement 0 3) x) =
      difference σ (rootElement 0 3) (difference σ (rootElement 2 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange14
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 3) (difference σ (rootElement 1 4) x) =
      difference σ (rootElement 1 4) (difference σ (rootElement 1 3) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange15
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 4) (difference σ (rootElement 2 4) x) =
      difference σ (rootElement 2 4) (difference σ (rootElement 1 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange16
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 4) (difference σ (rootElement 0 3) x) =
      difference σ (rootElement 0 3) (difference σ (rootElement 1 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange17
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 3 4) (difference σ (rootElement 2 0) x) =
      difference σ (rootElement 2 0) (difference σ (rootElement 3 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange18
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 4) (difference σ (rootElement 2 0) x) =
      difference σ (rootElement 2 0) (difference σ (rootElement 1 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange19
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 2) (difference σ (rootElement 1 4) x) =
      difference σ (rootElement 1 4) (difference σ (rootElement 1 2) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange20
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 2) (difference σ (rootElement 3 4) x) =
      difference σ (rootElement 3 4) (difference σ (rootElement 1 2) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange21
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 4) (difference σ (rootElement 3 4) x) =
      difference σ (rootElement 3 4) (difference σ (rootElement 1 4) x) :=
  difference_commute σ (by decide +kernel) x

private theorem exchange22
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) (x : V) :
    difference σ (rootElement 1 2) (difference σ (rootElement 4 3) x) =
      difference σ (rootElement 4 3) (difference σ (rootElement 1 2) x) :=
  difference_commute σ (by decide +kernel) x

private theorem action0 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 4) (σ w0 v) = σ w1 v := by
  apply difference_step h (rootElement 2 4) w0 w1
    [2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action1 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 0) (σ w1 v) = σ w2 v := by
  apply difference_step h (rootElement 2 0) w1 w2
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action2 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 2) (σ w2 v) = σ w1 v := by
  apply difference_step h (rootElement 0 2) w2 w1
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action3 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 1) (σ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action4 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 4) (σ w3 v) = σ w4 v := by
  apply difference_step h (rootElement 2 4) w3 w4
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action5 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w4 v) = σ w5 v := by
  apply difference_step h (rootElement 1 4) w4 w5
    [2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action6 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 1) (σ w5 v) = σ w2 v := by
  apply difference_step h (rootElement 0 1) w5 w2
    [] []
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action7 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 4) (σ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action8 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 4) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action9 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 4) (σ w6 v) = σ w0 v := by
  apply difference_step h (rootElement 0 4) w6 w0
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action10 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 1) (σ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action11 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 1) (σ w7 v) = σ w6 v := by
  apply difference_step h (rootElement 0 1) w7 w6
    [] []
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action12 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action13 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w5
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action14 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w6
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action15 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w7
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action16 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w8 v) = σ w9 v := by
  apply difference_step h (rootElement 1 3) w8 w9
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action17 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 4 3) (σ w9 v) = σ w10 v := by
  apply difference_step h (rootElement 4 3) w9 w10
    [3, 2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action18 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 4) (σ w10 v) = σ w11 v := by
  apply difference_step h (rootElement 2 4) w10 w11
    [2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action19 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w11
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action20 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 4) (σ w12 v) = σ w13 v := by
  apply difference_step h (rootElement 2 4) w12 w13
    [3, 2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action21 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w13 v) = σ w8 v := by
  apply difference_step h (rootElement 1 2) w13 w8
    [2] [2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action22 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 3) (σ w9 v) = σ w14 v := by
  apply difference_step h (rootElement 0 3) w9 w14
    [] [2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action23 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w2
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action24 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w5
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action25 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w6
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action26 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w7
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action27 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w11 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w11
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action28 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 2 3) (σ w13 v) = σ w15 v := by
  apply difference_step h (rootElement 2 3) w13 w15
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action29 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 0 3) (σ w15 v) = σ w2 v := by
  apply difference_step h (rootElement 0 3) w15 w2
    [] [2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action30 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w15 v) = σ w5 v := by
  apply difference_step h (rootElement 1 3) w15 w5
    [2] [2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action31 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action32 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action33 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w7 v) = σ w10 v := by
  apply difference_step h (rootElement 1 4) w7 w10
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action34 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w11
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action35 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w11
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action36 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w13
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action37 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 3) (σ w16 v) = σ w7 v := by
  apply difference_step h (rootElement 1 3) w16 w7
    [2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action38 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 3 4) (σ w0 v) = σ w17 v := by
  apply difference_step h (rootElement 3 4) w0 w17
    [3, 2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action39 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w17 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w17
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action40 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w3 v) = σ w7 v := by
  apply difference_step h (rootElement 1 2) w3 w7
    [2] [2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action41 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 3 4) (σ w10 v) = σ w9 v := by
  apply difference_step h (rootElement 3 4) w10 w9
    [3, 2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action42 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w9
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action43 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w6
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action44 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w9
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action45 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 2) (σ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w8
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action46 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 1 4) (σ w12 v) = σ w8 v := by
  apply difference_step h (rootElement 1 4) w12 w8
    [2] [3, 2]
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action47 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 3 4) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w12
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action48 (h : LocalHighestVector σ {0, 1} v) :
    difference σ (rootElement 3 4) (σ w16 v) = σ w12 v := by
  apply difference_step h (rootElement 3 4) w16 w12
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private def vectors (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (v : V) : Fin 9 → V :=
  ![difference σ (rootElement 2 0) (σ w0 v), difference σ (rootElement 1 4) (σ w3 v), σ w6 v, σ w7 v, difference σ (rootElement 4 3) (σ w8 v), difference σ (rootElement 0 3) (σ w12 v), σ w12 v, σ w16 v, σ w3 v]

private def extractors (σ : Representation (ZMod 2) SL5TenDimensional.Group V) :
    Fin 9 → V →ₗ[ZMod 2] V :=
  ![(difference σ (rootElement 0 2)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 0 1)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 0 4)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id))),
    (difference σ (rootElement 1 3)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 1 2)).comp ((difference σ (rootElement 1 3)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id))),
    (difference σ (rootElement 1 3)).comp ((difference σ (rootElement 2 3)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id))),
    (difference σ (rootElement 1 3)).comp ((difference σ (rootElement 1 4)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id))),
    (difference σ (rootElement 1 2)).comp ((difference σ (rootElement 1 4)).comp ((difference σ (rootElement 3 4)).comp (LinearMap.id)))]

/-- This support forces nine independent cosets modulo the literal radical fixed space. -/
theorem nine_le_fixedCodim [FiniteDimensional (ZMod 2) V]
    (h : LocalHighestVector σ {0, 1} v) (hv : v ≠ 0) :
    9 ≤ fixedCodim σ (radicalRootGroup 1) := by
  apply fixedCodim_ge_of_triangular σ 1 (vectors σ v) (extractors σ)
  · intro i
    fin_cases i
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 2)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 1)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 4)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 3)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 2)).comp ((difference σ (rootElement 1 3)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 3)).comp ((difference σ (rootElement 2 3)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 3)).comp ((difference σ (rootElement 1 4)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 2)))
      exact fixedSpace_le_ker_radical_difference σ 1 2 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 2)).comp ((difference σ (rootElement 1 4)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 3)))
      exact fixedSpace_le_ker_radical_difference σ 1 3 _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference σ (rootElement 0 1) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v))) = 0
      rw [exchange0 σ, action0 h, action1 h, action3 h]
    · change difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v))) = 0
      rw [exchange0 σ, action0 h, action1 h, action7 h]
    · change difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v))) = 0
      rw [exchange1 σ, action4 h, action5 h, action8 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v)))) = 0
      rw [exchange0 σ, action0 h, action1 h, action7 h, map_zero]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v)))) = 0
      rw [exchange1 σ, action4 h, action5 h, action8 h, map_zero]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (σ w6 v))) = 0
      rw [exchange2 σ, action9 h, action0 h, action10 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v))) = 0
      rw [exchange0 σ, action0 h, action1 h, action12 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v))) = 0
      rw [exchange1 σ, action4 h, action5 h, action13 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w6 v)) = 0
      rw [exchange5 σ, action14 h, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w7 v)) = 0
      rw [exchange5 σ, action15 h, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v)))) = 0
      rw [exchange0 σ, action0 h, action1 h, action12 h, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v)))) = 0
      rw [exchange1 σ, action4 h, action5 h, action13 h, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w6 v))) = 0
      rw [exchange5 σ, action14 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w7 v))) = 0
      rw [exchange5 σ, action15 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 4 3) (σ w8 v)))) = 0
      rw [exchange5 σ, exchange6 σ, action16 h, action17 h, action18 h, action19 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v)))) = 0
      rw [exchange0 σ, action0 h, action1 h, action23 h, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v)))) = 0
      rw [exchange1 σ, action4 h, action5 h, action24 h, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w6 v))) = 0
      rw [exchange11 σ, action25 h, map_zero, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w7 v))) = 0
      rw [exchange11 σ, action26 h, map_zero, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (difference σ (rootElement 4 3) (σ w8 v)))) = 0
      rw [exchange12 σ, exchange5 σ, exchange6 σ, action16 h, action17 h, action18 h, action27 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (difference σ (rootElement 0 3) (σ w12 v)))) = 0
      rw [exchange7 σ, action20 h, exchange13 σ, action28 h, action29 h, action12 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v)))) = 0
      rw [exchange0 σ, action0 h, action1 h, action31 h, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v)))) = 0
      rw [exchange1 σ, action4 h, action5 h, action32 h, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (σ w6 v))) = 0
      rw [exchange14 σ, exchange5 σ, action14 h, map_zero, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (σ w7 v))) = 0
      rw [exchange15 σ, action33 h, action18 h, action34 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (difference σ (rootElement 4 3) (σ w8 v)))) = 0
      rw [exchange14 σ, exchange5 σ, exchange6 σ, action16 h, action17 h, action18 h, action35 h]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (difference σ (rootElement 0 3) (σ w12 v)))) = 0
      rw [exchange7 σ, action20 h, exchange16 σ, action36 h, map_zero, map_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (σ w12 v))) = 0
      rw [action20 h, action36 h, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (difference σ (rootElement 2 0) (σ w0 v)))) = 0
      rw [exchange17 σ, action38 h, exchange18 σ, action39 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (difference σ (rootElement 1 4) (σ w3 v)))) = 0
      rw [exchange19 σ, exchange20 σ, exchange19 σ, action40 h, action33 h, action41 h, action42 h]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (σ w6 v))) = 0
      rw [exchange19 σ, exchange20 σ, action43 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (σ w7 v))) = 0
      rw [exchange21 σ, action33 h, action41 h, action44 h]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (difference σ (rootElement 4 3) (σ w8 v)))) = 0
      rw [exchange19 σ, exchange20 σ, exchange22 σ, action45 h, map_zero, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (difference σ (rootElement 0 3) (σ w12 v)))) = 0
      rw [exchange21 σ, exchange16 σ, action46 h, exchange20 σ, exchange9 σ, action45 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (σ w12 v))) = 0
      rw [action47 h, map_zero, map_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (σ w16 v))) = 0
      rw [action48 h, action46 h, action45 h]
  · intro i
    fin_cases i
    · change difference σ (rootElement 0 2) (difference σ (rootElement 2 4) (difference σ (rootElement 2 0) (σ w0 v))) ≠ 0
      rw [exchange0 σ, action0 h, action1 h, action2 h]
      exact translate_ne_zero σ w1 hv
    · change difference σ (rootElement 0 1) (difference σ (rootElement 2 4) (difference σ (rootElement 1 4) (σ w3 v))) ≠ 0
      rw [exchange1 σ, action4 h, action5 h, action6 h]
      exact translate_ne_zero σ w2 hv
    · change difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (σ w6 v)) ≠ 0
      rw [exchange2 σ, action9 h, action0 h]
      exact translate_ne_zero σ w1 hv
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (difference σ (rootElement 2 4) (σ w7 v))) ≠ 0
      rw [exchange3 σ, exchange4 σ, action11 h, exchange2 σ, action9 h, action0 h]
      exact translate_ne_zero σ w1 hv
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 4 3) (σ w8 v))) ≠ 0
      rw [exchange5 σ, exchange6 σ, action16 h, action17 h, action18 h]
      exact translate_ne_zero σ w11 hv
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (difference σ (rootElement 0 3) (σ w12 v)))) ≠ 0
      rw [exchange7 σ, action20 h, exchange8 σ, exchange9 σ, action21 h, exchange10 σ, action16 h, action22 h]
      exact translate_ne_zero σ w14 hv
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w12 v))) ≠ 0
      rw [action20 h, action28 h, action30 h]
      exact translate_ne_zero σ w5 hv
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (difference σ (rootElement 2 4) (σ w16 v))) ≠ 0
      rw [exchange14 σ, exchange5 σ, action37 h, exchange15 σ, action33 h, action18 h]
      exact translate_ne_zero σ w11 hv
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 4) (difference σ (rootElement 3 4) (σ w3 v))) ≠ 0
      rw [exchange19 σ, exchange20 σ, action40 h, exchange21 σ, action33 h, action41 h]
      exact translate_ne_zero σ w9 hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension.End1Support01
