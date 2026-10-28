module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic.Data

/-!
# Checked triangle and orbit-transport certificates

An incident pair (x, φ), with φ(x) = 0, represents the rank-one matrix xφ.
The 41 triangles below are translates of the two active root relations;
root words fixing the highest vector identify their three orbit vectors.
Summing those triangles checks conjugation by each adjacent exchange and
by the transvection I + E₀₁ on the twenty root and four diagonal vectors.
Every finite matrix identity is checked by kernel reduction. The Python
search in `source/` only selects witnesses; it is not part of the proof.

Source: GM, *Classification of 2F-modules, II*, Lemma 4.5 step 2, pp.23–24.
`Geometry` combines these equalities in the generator action table.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Representation
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

private def triangleMatrix2 : Group := matrixElement (!![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle2 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 5 + orbit σ v 25 + orbit σ v 37 = 0 := by
  apply triangle_relation h triangleMatrix2 (representative 5) (representative 25) (representative 37) 0 (by decide)
    [4, 10, 4] [] [0] <;> decide +kernel

private def triangleMatrix4 : Group := matrixElement (!![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle4 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 5 + orbit σ v 43 + orbit σ v 55 = 0 := by
  apply triangle_relation h triangleMatrix4 (representative 5) (representative 43) (representative 55) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix5 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle5 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 0 + orbit σ v 3 + orbit σ v 4 = 0 := by
  apply triangle_relation h triangleMatrix5 (representative 0) (representative 3) (representative 4) 3 (by decide)
    [] [4, 10, 4, 7, 12, 7] [] <;> decide +kernel

private def triangleMatrix6 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle6 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 15 + orbit σ v 25 + orbit σ v 40 = 0 := by
  apply triangle_relation h triangleMatrix6 (representative 15) (representative 25) (representative 40) 0 (by decide)
    [4, 10, 4] [4, 10, 4] [4, 10, 4, 0] <;> decide +kernel

private def triangleMatrix8 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle8 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 15 + orbit σ v 43 + orbit σ v 59 = 0 := by
  apply triangle_relation h triangleMatrix8 (representative 15) (representative 43) (representative 59) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [4, 10, 4] [4, 10, 4, 0] <;> decide +kernel

private def triangleMatrix10 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0]) (!![0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle10 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 25 + orbit σ v 43 + orbit σ v 62 = 0 := by
  apply triangle_relation h triangleMatrix10 (representative 25) (representative 43) (representative 62) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

private def triangleMatrix14 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle14 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 0 + orbit σ v 26 + orbit σ v 30 = 0 := by
  apply triangle_relation h triangleMatrix14 (representative 0) (representative 26) (representative 30) 0 (by decide)
    [4, 10, 4] [] [0] <;> decide +kernel

private def triangleMatrix16 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle16 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 0 + orbit σ v 44 + orbit σ v 48 = 0 := by
  apply triangle_relation h triangleMatrix16 (representative 0) (representative 44) (representative 48) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix24 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle24 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 1 + orbit σ v 6 + orbit σ v 10 = 0 := by
  apply triangle_relation h triangleMatrix24 (representative 1) (representative 6) (representative 10) 0 (by decide)
    [] [] [0] <;> decide +kernel

private def triangleMatrix25 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0]) (!![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle25 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 15 + orbit σ v 16 + orbit σ v 17 = 0 := by
  apply triangle_relation h triangleMatrix25 (representative 15) (representative 16) (representative 17) 3 (by decide)
    [4, 10, 4, 7, 12, 7] [4, 10, 4, 7, 12, 7] [] <;> decide +kernel

private def triangleMatrix26 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle26 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 1 + orbit σ v 28 + orbit σ v 31 = 0 := by
  apply triangle_relation h triangleMatrix26 (representative 1) (representative 28) (representative 31) 0 (by decide)
    [4, 10, 4] [] [0] <;> decide +kernel

private def triangleMatrix28 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle28 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 1 + orbit σ v 46 + orbit σ v 49 = 0 := by
  apply triangle_relation h triangleMatrix28 (representative 1) (representative 46) (representative 49) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix36 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (by decide +kernel)
theorem triangle36 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 2 + orbit σ v 7 + orbit σ v 11 = 0 := by
  apply triangle_relation h triangleMatrix36 (representative 2) (representative 7) (representative 11) 0 (by decide)
    [] [] [0] <;> decide +kernel

private def triangleMatrix37 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0]) (!![0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle37 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 25 + orbit σ v 26 + orbit σ v 27 = 0 := by
  apply triangle_relation h triangleMatrix37 (representative 25) (representative 26) (representative 27) 3 (by decide)
    [4, 10, 4, 7, 12, 7] [4, 10, 4, 7, 12, 7] [] <;> decide +kernel

private def triangleMatrix38 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (by decide +kernel)
theorem triangle38 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 2 + orbit σ v 18 + orbit σ v 21 = 0 := by
  apply triangle_relation h triangleMatrix38 (representative 2) (representative 18) (representative 21) 0 (by decide)
    [4, 10, 4] [] [0] <;> decide +kernel

private def triangleMatrix40 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]) (by decide +kernel)
theorem triangle40 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 2 + orbit σ v 47 + orbit σ v 50 = 0 := by
  apply triangle_relation h triangleMatrix40 (representative 2) (representative 47) (representative 50) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix48 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]) (by decide +kernel)
theorem triangle48 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 3 + orbit σ v 8 + orbit σ v 13 = 0 := by
  apply triangle_relation h triangleMatrix48 (representative 3) (representative 8) (representative 13) 0 (by decide)
    [] [] [0] <;> decide +kernel

private def triangleMatrix49 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0]) (!![0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle49 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 43 + orbit σ v 44 + orbit σ v 45 = 0 := by
  apply triangle_relation h triangleMatrix49 (representative 43) (representative 44) (representative 45) 3 (by decide)
    [4, 10, 4, 7, 12, 7] [4, 10, 4, 7, 12, 7] [] <;> decide +kernel

private def triangleMatrix50 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]) (by decide +kernel)
theorem triangle50 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 3 + orbit σ v 19 + orbit σ v 23 = 0 := by
  apply triangle_relation h triangleMatrix50 (representative 3) (representative 19) (representative 23) 0 (by decide)
    [4, 10, 4] [] [0] <;> decide +kernel

private def triangleMatrix52 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]) (!![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]) (by decide +kernel)
theorem triangle52 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 3 + orbit σ v 29 + orbit σ v 35 = 0 := by
  apply triangle_relation h triangleMatrix52 (representative 3) (representative 29) (representative 35) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix413 : Group := matrixElement (!![1, 0, 0, 0, 0; 1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 1, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle413 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 9 + orbit σ v 11 + orbit σ v 12 = 0 := by
  apply triangle_relation h triangleMatrix413 (representative 9) (representative 11) (representative 12) 3 (by decide)
    [7, 12, 7, 3] [4, 10, 4, 7, 12, 7, 2] [2, 3] <;> decide +kernel

private def triangleMatrix415 : Group := matrixElement (!![1, 0, 0, 0, 0; 1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle415 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 9 + orbit σ v 13 + orbit σ v 14 = 0 := by
  apply triangle_relation h triangleMatrix415 (representative 9) (representative 13) (representative 14) 3 (by decide)
    [3] [4, 10, 4, 7, 12, 7, 2] [2, 3] <;> decide +kernel

private def triangleMatrix429 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0; 1, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle429 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 20 + orbit σ v 21 + orbit σ v 22 = 0 := by
  apply triangle_relation h triangleMatrix429 (representative 20) (representative 21) (representative 22) 3 (by decide)
    [7, 12, 7, 3] [4, 10, 4, 7, 12, 7, 2] [2, 3] <;> decide +kernel

private def triangleMatrix431 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle431 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 20 + orbit σ v 23 + orbit σ v 24 = 0 := by
  apply triangle_relation h triangleMatrix431 (representative 20) (representative 23) (representative 24) 3 (by decide)
    [3] [4, 10, 4, 7, 12, 7, 2] [2, 3] <;> decide +kernel

private def triangleMatrix453 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle453 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 30 + orbit σ v 32 + orbit σ v 33 = 0 := by
  apply triangle_relation h triangleMatrix453 (representative 30) (representative 32) (representative 33) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2, 3, 9] <;> decide +kernel

private def triangleMatrix457 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle457 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 31 + orbit σ v 32 + orbit σ v 34 = 0 := by
  apply triangle_relation h triangleMatrix457 (representative 31) (representative 32) (representative 34) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [7, 12, 7, 3] [2, 3, 9] <;> decide +kernel

private def triangleMatrix465 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0]) (by decide +kernel)
theorem triangle465 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 32 + orbit σ v 35 + orbit σ v 36 = 0 := by
  apply triangle_relation h triangleMatrix465 (representative 32) (representative 35) (representative 36) 3 (by decide)
    [3] [4, 10, 4, 7, 12, 7, 2] [2, 3] <;> decide +kernel

private def triangleMatrix467 : Group := matrixElement (!![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 1, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle467 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 37 + orbit σ v 38 + orbit σ v 39 = 0 := by
  apply triangle_relation h triangleMatrix467 (representative 37) (representative 38) (representative 39) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2] <;> decide +kernel

private def triangleMatrix481 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 1, 0, 0, 1, 0; 0, 0, 1, 0, 0]) (!![0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 1, 0; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle481 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 40 + orbit σ v 41 + orbit σ v 42 = 0 := by
  apply triangle_relation h triangleMatrix481 (representative 40) (representative 41) (representative 42) 3 (by decide)
    [7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2] <;> decide +kernel

private def triangleMatrix497 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1; 0, 1, 0, 0, 0]) (by decide +kernel)
theorem triangle497 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 48 + orbit σ v 51 + orbit σ v 52 = 0 := by
  apply triangle_relation h triangleMatrix497 (representative 48) (representative 51) (representative 52) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2, 3, 9] <;> decide +kernel

private def triangleMatrix501 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 1, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1; 0, 0, 1, 0, 0]) (by decide +kernel)
theorem triangle501 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 49 + orbit σ v 51 + orbit σ v 53 = 0 := by
  apply triangle_relation h triangleMatrix501 (representative 49) (representative 51) (representative 53) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [7, 12, 7, 3] [2, 3, 9] <;> decide +kernel

private def triangleMatrix507 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 1, 0, 0, 1, 0]) (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 1; 0, 0, 0, 1, 0]) (by decide +kernel)
theorem triangle507 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 50 + orbit σ v 51 + orbit σ v 54 = 0 := by
  apply triangle_relation h triangleMatrix507 (representative 50) (representative 51) (representative 54) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [3] [2, 3, 9] <;> decide +kernel

private def triangleMatrix510 : Group := matrixElement (!![1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1]) (by decide +kernel)
theorem triangle510 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 4 + orbit σ v 56 + orbit σ v 58 = 0 := by
  apply triangle_relation h triangleMatrix510 (representative 4) (representative 56) (representative 58) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [] [0] <;> decide +kernel

private def triangleMatrix511 : Group := matrixElement (!![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 1, 0]) (!![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle511 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 55 + orbit σ v 56 + orbit σ v 57 = 0 := by
  apply triangle_relation h triangleMatrix511 (representative 55) (representative 56) (representative 57) 3 (by decide)
    [4, 10, 4, 7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2] <;> decide +kernel

private def triangleMatrix525 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 1, 0]) (!![0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 1; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle525 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 59 + orbit σ v 60 + orbit σ v 61 = 0 := by
  apply triangle_relation h triangleMatrix525 (representative 59) (representative 60) (representative 61) 3 (by decide)
    [7, 12, 7, 2] [4, 10, 4, 7, 12, 7, 3] [2] <;> decide +kernel

private def triangleMatrix539 : Group := matrixElement (!![0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 1, 0, 0, 1, 0]) (!![0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 1, 0, 0, 0, 0]) (by decide +kernel)
theorem triangle539 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 62 + orbit σ v 63 + orbit σ v 64 = 0 := by
  apply triangle_relation h triangleMatrix539 (representative 62) (representative 63) (representative 64) 3 (by decide)
    [2] [4, 10, 4, 7, 12, 7, 3] [2] <;> decide +kernel

private def triangleMatrix826 : Group := matrixElement (!![1, 1, 0, 0, 1; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 1, 1, 0, 1, 0]) (by decide +kernel)
theorem triangle826 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 12 + orbit σ v 33 + orbit σ v 39 = 0 := by
  apply triangle_relation h triangleMatrix826 (representative 12) (representative 33) (representative 39) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

private def triangleMatrix844 : Group := matrixElement (!![1, 1, 0, 0, 1; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0]) (!![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 1, 0, 1, 1, 0]) (by decide +kernel)
theorem triangle844 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 22 + orbit σ v 34 + orbit σ v 42 = 0 := by
  apply triangle_relation h triangleMatrix844 (representative 22) (representative 34) (representative 42) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

private def triangleMatrix870 : Group := matrixElement (!![1, 1, 0, 0, 1; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 1, 0, 0, 1]) (by decide +kernel)
theorem triangle870 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 14 + orbit σ v 52 + orbit σ v 57 = 0 := by
  apply triangle_relation h triangleMatrix870 (representative 14) (representative 52) (representative 57) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

private def triangleMatrix888 : Group := matrixElement (!![1, 1, 0, 0, 1; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]) (!![0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 1, 0, 1, 0, 1]) (by decide +kernel)
theorem triangle888 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 24 + orbit σ v 53 + orbit σ v 61 = 0 := by
  apply triangle_relation h triangleMatrix888 (representative 24) (representative 53) (representative 61) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

private def triangleMatrix920 : Group := matrixElement (!![1, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0]) (!![0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 1, 1]) (by decide +kernel)
theorem triangle920 (h : LocalHighestVector σ {0, 3} v) :
    orbit σ v 36 + orbit σ v 54 + orbit σ v 64 = 0 := by
  apply triangle_relation h triangleMatrix920 (representative 36) (representative 54) (representative 64) 0 (by decide)
    [5, 11, 5, 7, 12, 7] [5, 11, 5, 7, 12, 7] [5, 11, 5, 0, 7, 12, 7] <;> decide +kernel

theorem transport0_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 0) = orbit σ v 5 := by
  change σ (generator 0) (σ (representative 0) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 5) [] (by decide +kernel)

theorem transport0_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 1) = orbit σ v 6 := by
  change σ (generator 0) (σ (representative 1) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 6) [] (by decide +kernel)

theorem transport0_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 2) = orbit σ v 7 := by
  change σ (generator 0) (σ (representative 2) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 7) [] (by decide +kernel)

theorem transport0_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 3) = orbit σ v 8 := by
  change σ (generator 0) (σ (representative 3) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 8) [] (by decide +kernel)

theorem transport0_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 5) = orbit σ v 0 := by
  change σ (generator 0) (σ (representative 5) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 0) [] (by decide +kernel)

theorem transport0_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 6) = orbit σ v 1 := by
  change σ (generator 0) (σ (representative 6) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 1) [] (by decide +kernel)

theorem transport0_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 7) = orbit σ v 2 := by
  change σ (generator 0) (σ (representative 7) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 2) [] (by decide +kernel)

theorem transport0_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 8) = orbit σ v 3 := by
  change σ (generator 0) (σ (representative 8) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 3) [] (by decide +kernel)

theorem transport0_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 15) = orbit σ v 16 := by
  change σ (generator 0) (σ (representative 15) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 16) [] (by decide +kernel)

theorem transport0_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 16) = orbit σ v 15 := by
  change σ (generator 0) (σ (representative 16) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 15) [] (by decide +kernel)

theorem transport0_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 18) = orbit σ v 18 := by
  change σ (generator 0) (σ (representative 18) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 18) [4, 10, 4] (by decide +kernel)

theorem transport0_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 19) = orbit σ v 19 := by
  change σ (generator 0) (σ (representative 19) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 19) [4, 10, 4] (by decide +kernel)

theorem transport0_25 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 25) = orbit σ v 26 := by
  change σ (generator 0) (σ (representative 25) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 26) [] (by decide +kernel)

theorem transport0_26 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 26) = orbit σ v 25 := by
  change σ (generator 0) (σ (representative 26) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 25) [] (by decide +kernel)

theorem transport0_28 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 28) = orbit σ v 28 := by
  change σ (generator 0) (σ (representative 28) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 28) [4, 10, 4] (by decide +kernel)

theorem transport0_29 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 29) = orbit σ v 29 := by
  change σ (generator 0) (σ (representative 29) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 29) [4, 10, 4] (by decide +kernel)

theorem transport0_43 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 43) = orbit σ v 44 := by
  change σ (generator 0) (σ (representative 43) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 44) [] (by decide +kernel)

theorem transport0_44 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 44) = orbit σ v 43 := by
  change σ (generator 0) (σ (representative 44) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 43) [] (by decide +kernel)

theorem transport0_46 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 46) = orbit σ v 46 := by
  change σ (generator 0) (σ (representative 46) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 46) [4, 10, 4] (by decide +kernel)

theorem transport0_47 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 47) = orbit σ v 47 := by
  change σ (generator 0) (σ (representative 47) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 47) [4, 10, 4] (by decide +kernel)

theorem transport0_51 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 51) = orbit σ v 56 := by
  change σ (generator 0) (σ (representative 51) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 56) [] (by decide +kernel)

theorem transport0_56 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 56) = orbit σ v 51 := by
  change σ (generator 0) (σ (representative 56) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 51) [] (by decide +kernel)

theorem transport0_60 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 60) = orbit σ v 60 := by
  change σ (generator 0) (σ (representative 60) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 60) [4, 10, 4] (by decide +kernel)

theorem transport0_63 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (orbit σ v 63) = orbit σ v 63 := by
  change σ (generator 0) (σ (representative 63) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 63) [4, 10, 4] (by decide +kernel)

theorem transport1_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 0) = orbit σ v 1 := by
  change σ (generator 1) (σ (representative 0) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 1) [] (by decide +kernel)

theorem transport1_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 1) = orbit σ v 0 := by
  change σ (generator 1) (σ (representative 1) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 0) [] (by decide +kernel)

theorem transport1_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 2) = orbit σ v 2 := by
  change σ (generator 1) (σ (representative 2) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 2) [4, 10, 4] (by decide +kernel)

theorem transport1_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 3) = orbit σ v 3 := by
  change σ (generator 1) (σ (representative 3) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 3) [4, 10, 4] (by decide +kernel)

theorem transport1_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 5) = orbit σ v 15 := by
  change σ (generator 1) (σ (representative 5) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 15) [] (by decide +kernel)

theorem transport1_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 6) = orbit σ v 16 := by
  change σ (generator 1) (σ (representative 6) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 16) [] (by decide +kernel)

theorem transport1_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 7) = orbit σ v 18 := by
  change σ (generator 1) (σ (representative 7) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 18) [] (by decide +kernel)

theorem transport1_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 8) = orbit σ v 19 := by
  change σ (generator 1) (σ (representative 8) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 19) [] (by decide +kernel)

theorem transport1_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 15) = orbit σ v 5 := by
  change σ (generator 1) (σ (representative 15) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 5) [] (by decide +kernel)

theorem transport1_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 16) = orbit σ v 6 := by
  change σ (generator 1) (σ (representative 16) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 6) [] (by decide +kernel)

theorem transport1_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 18) = orbit σ v 7 := by
  change σ (generator 1) (σ (representative 18) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 7) [] (by decide +kernel)

theorem transport1_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 19) = orbit σ v 8 := by
  change σ (generator 1) (σ (representative 19) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 8) [] (by decide +kernel)

theorem transport1_25 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 25) = orbit σ v 25 := by
  change σ (generator 1) (σ (representative 25) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 25) [4, 10, 4] (by decide +kernel)

theorem transport1_26 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 26) = orbit σ v 28 := by
  change σ (generator 1) (σ (representative 26) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 28) [] (by decide +kernel)

theorem transport1_28 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 28) = orbit σ v 26 := by
  change σ (generator 1) (σ (representative 28) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 26) [] (by decide +kernel)

theorem transport1_29 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 29) = orbit σ v 29 := by
  change σ (generator 1) (σ (representative 29) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 29) [7, 12, 7] (by decide +kernel)

theorem transport1_43 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 43) = orbit σ v 43 := by
  change σ (generator 1) (σ (representative 43) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 43) [4, 10, 4] (by decide +kernel)

theorem transport1_44 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 44) = orbit σ v 46 := by
  change σ (generator 1) (σ (representative 44) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 46) [] (by decide +kernel)

theorem transport1_46 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 46) = orbit σ v 44 := by
  change σ (generator 1) (σ (representative 46) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 44) [] (by decide +kernel)

theorem transport1_47 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 47) = orbit σ v 47 := by
  change σ (generator 1) (σ (representative 47) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 47) [7, 12, 7] (by decide +kernel)

theorem transport1_51 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 51) = orbit σ v 51 := by
  change σ (generator 1) (σ (representative 51) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 51) [4, 10, 4] (by decide +kernel)

theorem transport1_56 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 56) = orbit σ v 60 := by
  change σ (generator 1) (σ (representative 56) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 60) [] (by decide +kernel)

theorem transport1_60 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 60) = orbit σ v 56 := by
  change σ (generator 1) (σ (representative 60) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 56) [] (by decide +kernel)

theorem transport1_63 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (orbit σ v 63) = orbit σ v 63 := by
  change σ (generator 1) (σ (representative 63) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 63) [7, 12, 7] (by decide +kernel)

theorem transport2_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 0) = orbit σ v 0 := by
  change σ (generator 2) (σ (representative 0) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 0) [4, 10, 4] (by decide +kernel)

theorem transport2_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 1) = orbit σ v 2 := by
  change σ (generator 2) (σ (representative 1) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 2) [] (by decide +kernel)

theorem transport2_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 2) = orbit σ v 1 := by
  change σ (generator 2) (σ (representative 2) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 1) [] (by decide +kernel)

theorem transport2_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 3) = orbit σ v 3 := by
  change σ (generator 2) (σ (representative 3) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 3) [7, 12, 7] (by decide +kernel)

theorem transport2_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 5) = orbit σ v 5 := by
  change σ (generator 2) (σ (representative 5) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 5) [4, 10, 4] (by decide +kernel)

theorem transport2_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 6) = orbit σ v 7 := by
  change σ (generator 2) (σ (representative 6) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 7) [] (by decide +kernel)

theorem transport2_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 7) = orbit σ v 6 := by
  change σ (generator 2) (σ (representative 7) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 6) [] (by decide +kernel)

theorem transport2_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 8) = orbit σ v 8 := by
  change σ (generator 2) (σ (representative 8) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 8) [7, 12, 7] (by decide +kernel)

theorem transport2_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 15) = orbit σ v 25 := by
  change σ (generator 2) (σ (representative 15) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 25) [] (by decide +kernel)

theorem transport2_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 16) = orbit σ v 26 := by
  change σ (generator 2) (σ (representative 16) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 26) [] (by decide +kernel)

theorem transport2_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 18) = orbit σ v 28 := by
  change σ (generator 2) (σ (representative 18) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 28) [] (by decide +kernel)

theorem transport2_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 19) = orbit σ v 29 := by
  change σ (generator 2) (σ (representative 19) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 29) [] (by decide +kernel)

theorem transport2_25 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 25) = orbit σ v 15 := by
  change σ (generator 2) (σ (representative 25) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 15) [] (by decide +kernel)

theorem transport2_26 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 26) = orbit σ v 16 := by
  change σ (generator 2) (σ (representative 26) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 16) [] (by decide +kernel)

theorem transport2_28 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 28) = orbit σ v 18 := by
  change σ (generator 2) (σ (representative 28) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 18) [] (by decide +kernel)

theorem transport2_29 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 29) = orbit σ v 19 := by
  change σ (generator 2) (σ (representative 29) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 19) [] (by decide +kernel)

theorem transport2_43 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 43) = orbit σ v 43 := by
  change σ (generator 2) (σ (representative 43) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 43) [7, 12, 7] (by decide +kernel)

theorem transport2_44 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 44) = orbit σ v 44 := by
  change σ (generator 2) (σ (representative 44) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 44) [7, 12, 7] (by decide +kernel)

theorem transport2_46 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 46) = orbit σ v 47 := by
  change σ (generator 2) (σ (representative 46) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 47) [] (by decide +kernel)

theorem transport2_47 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 47) = orbit σ v 46 := by
  change σ (generator 2) (σ (representative 47) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 46) [] (by decide +kernel)

theorem transport2_51 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 51) = orbit σ v 51 := by
  change σ (generator 2) (σ (representative 51) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 51) [7, 12, 7] (by decide +kernel)

theorem transport2_56 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 56) = orbit σ v 56 := by
  change σ (generator 2) (σ (representative 56) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 56) [7, 12, 7] (by decide +kernel)

theorem transport2_60 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 60) = orbit σ v 63 := by
  change σ (generator 2) (σ (representative 60) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 63) [] (by decide +kernel)

theorem transport2_63 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (orbit σ v 63) = orbit σ v 60 := by
  change σ (generator 2) (σ (representative 63) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 60) [] (by decide +kernel)

theorem transport3_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 0) = orbit σ v 0 := by
  change σ (generator 3) (σ (representative 0) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 0) [7, 12, 7] (by decide +kernel)

theorem transport3_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 1) = orbit σ v 1 := by
  change σ (generator 3) (σ (representative 1) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 1) [7, 12, 7] (by decide +kernel)

theorem transport3_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 2) = orbit σ v 3 := by
  change σ (generator 3) (σ (representative 2) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 3) [] (by decide +kernel)

theorem transport3_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 3) = orbit σ v 2 := by
  change σ (generator 3) (σ (representative 3) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 2) [] (by decide +kernel)

theorem transport3_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 5) = orbit σ v 5 := by
  change σ (generator 3) (σ (representative 5) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 5) [7, 12, 7] (by decide +kernel)

theorem transport3_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 6) = orbit σ v 6 := by
  change σ (generator 3) (σ (representative 6) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 6) [7, 12, 7] (by decide +kernel)

theorem transport3_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 7) = orbit σ v 8 := by
  change σ (generator 3) (σ (representative 7) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 8) [] (by decide +kernel)

theorem transport3_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 8) = orbit σ v 7 := by
  change σ (generator 3) (σ (representative 8) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 7) [] (by decide +kernel)

theorem transport3_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 15) = orbit σ v 15 := by
  change σ (generator 3) (σ (representative 15) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 15) [7, 12, 7] (by decide +kernel)

theorem transport3_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 16) = orbit σ v 16 := by
  change σ (generator 3) (σ (representative 16) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 16) [7, 12, 7] (by decide +kernel)

theorem transport3_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 18) = orbit σ v 19 := by
  change σ (generator 3) (σ (representative 18) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 19) [] (by decide +kernel)

theorem transport3_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 19) = orbit σ v 18 := by
  change σ (generator 3) (σ (representative 19) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 18) [] (by decide +kernel)

theorem transport3_25 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 25) = orbit σ v 43 := by
  change σ (generator 3) (σ (representative 25) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 43) [] (by decide +kernel)

theorem transport3_26 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 26) = orbit σ v 44 := by
  change σ (generator 3) (σ (representative 26) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 44) [] (by decide +kernel)

theorem transport3_28 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 28) = orbit σ v 46 := by
  change σ (generator 3) (σ (representative 28) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 46) [] (by decide +kernel)

theorem transport3_29 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 29) = orbit σ v 47 := by
  change σ (generator 3) (σ (representative 29) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 47) [] (by decide +kernel)

theorem transport3_43 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 43) = orbit σ v 25 := by
  change σ (generator 3) (σ (representative 43) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 25) [] (by decide +kernel)

theorem transport3_44 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 44) = orbit σ v 26 := by
  change σ (generator 3) (σ (representative 44) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 26) [] (by decide +kernel)

theorem transport3_46 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 46) = orbit σ v 28 := by
  change σ (generator 3) (σ (representative 46) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 28) [] (by decide +kernel)

theorem transport3_47 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 47) = orbit σ v 29 := by
  change σ (generator 3) (σ (representative 47) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 29) [] (by decide +kernel)

theorem transport3_51 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 51) = orbit σ v 32 := by
  change σ (generator 3) (σ (representative 51) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 32) [] (by decide +kernel)

theorem transport3_56 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 56) = orbit σ v 38 := by
  change σ (generator 3) (σ (representative 56) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 38) [] (by decide +kernel)

theorem transport3_60 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 60) = orbit σ v 41 := by
  change σ (generator 3) (σ (representative 60) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 41) [] (by decide +kernel)

theorem transport3_63 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (orbit σ v 63) = orbit σ v 63 := by
  change σ (generator 3) (σ (representative 63) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 63) [3] (by decide +kernel)

theorem transport4_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 0) = orbit σ v 0 := by
  change σ (generator 4) (σ (representative 0) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 0) [3] (by decide +kernel)

theorem transport4_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 1) = orbit σ v 1 := by
  change σ (generator 4) (σ (representative 1) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 1) [0] (by decide +kernel)

theorem transport4_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 2) = orbit σ v 2 := by
  change σ (generator 4) (σ (representative 2) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 2) [0] (by decide +kernel)

theorem transport4_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 3) = orbit σ v 3 := by
  change σ (generator 4) (σ (representative 3) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 3) [0] (by decide +kernel)

theorem transport4_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 5) = orbit σ v 9 := by
  change σ (generator 4) (σ (representative 5) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 9) [] (by decide +kernel)

theorem transport4_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 6) = orbit σ v 10 := by
  change σ (generator 4) (σ (representative 6) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 10) [] (by decide +kernel)

theorem transport4_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 7) = orbit σ v 11 := by
  change σ (generator 4) (σ (representative 7) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 11) [] (by decide +kernel)

theorem transport4_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 8) = orbit σ v 13 := by
  change σ (generator 4) (σ (representative 8) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 13) [] (by decide +kernel)

theorem transport4_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 15) = orbit σ v 17 := by
  change σ (generator 4) (σ (representative 15) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 17) [5, 11, 5, 7, 12, 7] (by decide +kernel)

theorem transport4_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 16) = orbit σ v 16 := by
  change σ (generator 4) (σ (representative 16) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 16) [6] (by decide +kernel)

theorem transport4_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 18) = orbit σ v 18 := by
  change σ (generator 4) (σ (representative 18) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 18) [4] (by decide +kernel)

theorem transport4_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 19) = orbit σ v 19 := by
  change σ (generator 4) (σ (representative 19) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 19) [4] (by decide +kernel)

theorem transport4_25 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 25) = orbit σ v 27 := by
  change σ (generator 4) (σ (representative 25) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 27) [5, 11, 5, 7, 12, 7] (by decide +kernel)

theorem transport4_26 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 26) = orbit σ v 26 := by
  change σ (generator 4) (σ (representative 26) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 26) [6] (by decide +kernel)

theorem transport4_28 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 28) = orbit σ v 28 := by
  change σ (generator 4) (σ (representative 28) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 28) [4] (by decide +kernel)

theorem transport4_29 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 29) = orbit σ v 29 := by
  change σ (generator 4) (σ (representative 29) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 29) [4] (by decide +kernel)

theorem transport4_43 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 43) = orbit σ v 45 := by
  change σ (generator 4) (σ (representative 43) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 45) [5, 11, 5, 7, 12, 7] (by decide +kernel)

theorem transport4_44 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 44) = orbit σ v 44 := by
  change σ (generator 4) (σ (representative 44) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 44) [6] (by decide +kernel)

theorem transport4_46 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 46) = orbit σ v 46 := by
  change σ (generator 4) (σ (representative 46) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 46) [4] (by decide +kernel)

theorem transport4_47 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 47) = orbit σ v 47 := by
  change σ (generator 4) (σ (representative 47) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 47) [4] (by decide +kernel)

theorem transport4_51 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 51) = orbit σ v 52 := by
  change σ (generator 4) (σ (representative 51) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 52) [5, 11, 5, 7, 12, 7] (by decide +kernel)

theorem transport4_56 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 56) = orbit σ v 58 := by
  change σ (generator 4) (σ (representative 56) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 58) [6] (by decide +kernel)

theorem transport4_60 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 60) = orbit σ v 60 := by
  change σ (generator 4) (σ (representative 60) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 60) [4] (by decide +kernel)

theorem transport4_63 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (orbit σ v 63) = orbit σ v 63 := by
  change σ (generator 4) (σ (representative 63) v) = _
  rw [← apply_mul]
  exact word_transport h _ (representative 63) [4] (by decide +kernel)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
