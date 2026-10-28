module

public import Theory.GroupTheory.BinaryCollection
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row00
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row01
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row02
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row03
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row04
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row05
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row06
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row07
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row08
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row09
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row10
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row11
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row12
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Row13

/-!
# Triangular collection for the fixed Rudvalis coordinates

Each row checks its square and inverse conjugates on all 4060 points.
The word supports lie in the later generators, so the checked rows give
successive binary extensions. This proves the triangular hypothesis for
exactly the fourteen generators used by `normalForm`.

Source: the untrusted data in `ElementaryCatalogue/source/certificates.json`,
with ATLAS attribution and inverse point convention in the adjacent README.
This is the concrete calculation needed for [Asc86b], quasithin printed p.511.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate.Coverage
open Theory.GroupTheory.BinaryCollection

private theorem triangular_13 :
    triangular (([13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 13 [] (squareWord 13)
    (conjugateWord 13) square_13 ?_ ?_ ?_ (by trivial)
  · intro j hj
    apply conjugate_13
    have hlt : ∀ j : Fin 14, j ∈ ([] : List (Fin 14)) → (13 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_12 :
    triangular (([12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 12 [13] (squareWord 12)
    (conjugateWord 12) square_12 ?_ ?_ ?_ triangular_13
  · intro j hj
    apply conjugate_12
    have hlt : ∀ j : Fin 14, j ∈ ([13] : List (Fin 14)) → (12 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_11 :
    triangular (([11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 11 [12, 13] (squareWord 11)
    (conjugateWord 11) square_11 ?_ ?_ ?_ triangular_12
  · intro j hj
    apply conjugate_11
    have hlt : ∀ j : Fin 14, j ∈ ([12, 13] : List (Fin 14)) → (11 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_10 :
    triangular (([10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 10 [11, 12, 13] (squareWord 10)
    (conjugateWord 10) square_10 ?_ ?_ ?_ triangular_11
  · intro j hj
    apply conjugate_10
    have hlt : ∀ j : Fin 14, j ∈ ([11, 12, 13] : List (Fin 14)) → (10 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_9 :
    triangular (([9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 9 [10, 11, 12, 13] (squareWord 9)
    (conjugateWord 9) square_9 ?_ ?_ ?_ triangular_10
  · intro j hj
    apply conjugate_9
    have hlt : ∀ j : Fin 14, j ∈ ([10, 11, 12, 13] : List (Fin 14)) → (9 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_8 :
    triangular (([8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 8 [9, 10, 11, 12, 13] (squareWord 8)
    (conjugateWord 8) square_8 ?_ ?_ ?_ triangular_9
  · intro j hj
    apply conjugate_8
    have hlt : ∀ j : Fin 14, j ∈ ([9, 10, 11, 12, 13] : List (Fin 14)) → (8 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_7 :
    triangular (([7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 7 [8, 9, 10, 11, 12, 13] (squareWord 7)
    (conjugateWord 7) square_7 ?_ ?_ ?_ triangular_8
  · intro j hj
    apply conjugate_7
    have hlt : ∀ j : Fin 14, j ∈ ([8, 9, 10, 11, 12, 13] : List (Fin 14)) → (7 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_6 :
    triangular (([6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 6 [7, 8, 9, 10, 11, 12, 13] (squareWord 6)
    (conjugateWord 6) square_6 ?_ ?_ ?_ triangular_7
  · intro j hj
    apply conjugate_6
    have hlt : ∀ j : Fin 14, j ∈ ([7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (6 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_5 :
    triangular (([5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 5 [6, 7, 8, 9, 10, 11, 12, 13] (squareWord 5)
    (conjugateWord 5) square_5 ?_ ?_ ?_ triangular_6
  · intro j hj
    apply conjugate_5
    have hlt : ∀ j : Fin 14, j ∈ ([6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (5 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_4 :
    triangular (([4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 4 [5, 6, 7, 8, 9, 10, 11, 12, 13] (squareWord 4)
    (conjugateWord 4) square_4 ?_ ?_ ?_ triangular_5
  · intro j hj
    apply conjugate_4
    have hlt : ∀ j : Fin 14, j ∈ ([5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (4 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_3 :
    triangular (([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (squareWord 3)
    (conjugateWord 3) square_3 ?_ ?_ ?_ triangular_4
  · intro j hj
    apply conjugate_3
    have hlt : ∀ j : Fin 14, j ∈ ([4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (3 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_2 :
    triangular (([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (squareWord 2)
    (conjugateWord 2) square_2 ?_ ?_ ?_ triangular_3
  · intro j hj
    apply conjugate_2
    have hlt : ∀ j : Fin 14, j ∈ ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (2 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_1 :
    triangular (([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (squareWord 1)
    (conjugateWord 1) square_1 ?_ ?_ ?_ triangular_2
  · intro j hj
    apply conjugate_1
    have hlt : ∀ j : Fin 14, j ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (1 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

private theorem triangular_0 :
    triangular (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)).map pcGenerator) := by
  apply triangular_cons_of_words pcGenerator 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (squareWord 0)
    (conjugateWord 0) square_0 ?_ ?_ ?_ triangular_1
  · intro j hj
    apply conjugate_0
    have hlt : ∀ j : Fin 14, j ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 14)) → (0 : Fin 14) < j := by
      decide +kernel
    exact hlt j hj
  · decide +kernel
  · decide +kernel

/-- The fixed coordinate generators satisfy the triangular binary relations. -/
public theorem pcGenerator_triangular : triangular (List.ofFn pcGenerator) := by
  change triangular (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] :
    List (Fin 14)).map pcGenerator)
  exact triangular_0

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate.Coverage
