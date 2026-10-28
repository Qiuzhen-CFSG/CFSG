module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Nine root displacements from endpoint highest-vector data

For each ordered pair `(i,j)`, `wij` is a coordinate permutation carrying
`(0,4)` to `(i,j)`. An endpoint highest vector is fixed by the exchanges of
coordinates 1, 2 and 3. Its upper-root fixedness and its two active rank-one
relations therefore determine the root differences used below, by the
`difference_zero` and `difference_step` rules. All finite matrix identities
are checked by kernel reduction. The coordinate permutations are represented
by their five images; their determinants use the permutation-sign theorem in
characteristic two, avoiding repeated expansion of long matrix products.

Let `dij = σ(rootElement i j) - 1`, and let an injective linear operator T
satisfy `dij T = T dji`. For the nine pairs
`01, 02, 03, 04, 12, 13, 14, 23, 24`, use the vectors
`σ(wij)v + T(σ(wij)v)`. In this order the extracting operators are
`d02, d23, d34, d02 d14, d12 d13, d13 d14, d13 d24, d23 d24, d24 d34`,
with the rightmost factor applied first. Each extractor kills all preceding
vectors and sends its own vector to a nonzero translate of v or its T-image.
The resulting triangular certificate gives nine independent vectors in
`range (T - 1)`, since the coefficient field has characteristic two.

The consumer `Graph.Endpoint` derives the literal intertwining identities
from the standard graph action on the marked SL₅. This argument uses only
local highest-vector data; it does not identify the module with the adjoint
module or assume absolute irreducibility.

Source application: Guralnick–Malle, *Classification of 2F-modules, II*,
author manuscript Proposition 4.8(3A), p.27; Aschbacher–Smith K.3.2,
printed pp.454–455 (PDF pp.465–466). This is a direct local-root proof of
the nine-dimensional estimate needed in that endpoint branch.
-/

public section

open Representation
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Endpoint
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) SL5TenDimensional.Group V} {v : V}

-- Over the binary field the sign of every coordinate permutation is one.
-- This structural determinant proof avoids enumerating a determinant for every word.
private def permutationElement (p : Equiv.Perm (Fin 5)) : SL5TenDimensional.Group :=
  ⟨p.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp] <;> decide⟩

private def w01 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 4, 1, 2, 3], ![0, 2, 3, 4, 1], by decide +kernel, by decide +kernel⟩
private def w02 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide +kernel, by decide +kernel⟩
private def w03 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide +kernel, by decide +kernel⟩
private def w04 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide +kernel, by decide +kernel⟩
private def w10 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 0, 1, 2, 3], ![1, 2, 3, 4, 0], by decide +kernel, by decide +kernel⟩
private def w12 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 4, 2, 3], ![1, 0, 3, 4, 2], by decide +kernel, by decide +kernel⟩
private def w13 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], by decide +kernel, by decide +kernel⟩
private def w14 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 2, 3, 4], ![1, 0, 2, 3, 4], by decide +kernel, by decide +kernel⟩
private def w20 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 1, 0, 2, 3], ![2, 1, 3, 4, 0], by decide +kernel, by decide +kernel⟩
private def w21 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 0, 2, 3], ![2, 0, 3, 4, 1], by decide +kernel, by decide +kernel⟩
private def w23 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 0, 4, 3], ![2, 0, 1, 4, 3], by decide +kernel, by decide +kernel⟩
private def w24 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide +kernel, by decide +kernel⟩
private def w30 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 1, 2, 0, 3], ![3, 1, 2, 4, 0], by decide +kernel, by decide +kernel⟩
private def w31 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 2, 0, 3], ![3, 0, 2, 4, 1], by decide +kernel, by decide +kernel⟩
private def w32 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 4, 0, 3], ![3, 0, 1, 4, 2], by decide +kernel, by decide +kernel⟩
private def w34 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 3, 0, 4], ![3, 0, 1, 2, 4], by decide +kernel, by decide +kernel⟩
private def w40 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 1, 2, 3, 0], ![4, 1, 2, 3, 0], by decide +kernel, by decide +kernel⟩
private def w41 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 2, 3, 0], ![4, 0, 2, 3, 1], by decide +kernel, by decide +kernel⟩
private def w42 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 4, 3, 0], ![4, 0, 1, 3, 2], by decide +kernel, by decide +kernel⟩
private def w43 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide +kernel, by decide +kernel⟩

private theorem action0 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 0 2) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w01
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action1 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 0) (σ w01 v) = σ w21 v := by
  apply difference_step h (rootElement 2 0) w01 w21
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action2 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 3) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w01
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action3 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 2) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w01
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action4 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 3) (σ w02 v) = σ w03 v := by
  apply difference_step h (rootElement 2 3) w02 w03
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action5 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 2) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w02
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action6 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w01
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action7 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w01
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action8 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w02
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action9 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w02
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action10 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w03 v) = σ w04 v := by
  apply difference_step h (rootElement 3 4) w03 w04
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action11 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w03
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action12 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w01 v) = σ w04 v := by
  apply difference_step h (rootElement 1 4) w01 w04
    [] [1, 2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action13 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w01
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action14 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 0 2) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w04
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action15 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w02
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action16 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w02
    [1, 2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action17 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w03
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action18 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w03
    [1, 2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action19 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w04
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action20 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w04 v) = σ w01 v := by
  apply difference_step h (rootElement 4 1) w04 w01
    [1, 2] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action21 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w01 v) = σ w03 v := by
  apply difference_step h (rootElement 1 3) w01 w03
    [2] [1, 2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action22 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w01
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action23 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 2) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w03
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action24 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w02
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action25 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w02
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action26 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w03
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action27 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w03 v) = σ w01 v := by
  apply difference_step h (rootElement 3 1) w03 w01
    [1, 2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action28 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 1) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w01
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action29 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w04
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action30 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w04
    [1, 2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action31 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w12
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action32 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w12 v) = σ w32 v := by
  apply difference_step h (rootElement 3 1) w12 w32
    [1] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action33 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 1) (σ w32 v) = σ w31 v := by
  apply difference_step h (rootElement 2 1) w32 w31
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action34 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action35 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w12 v) = σ w42 v := by
  apply difference_step h (rootElement 4 1) w12 w42
    [2, 1] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action36 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w42 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w42
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action37 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 4) (σ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w13
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action38 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 1) (σ w13 v) = σ w43 v := by
  apply difference_step h (rootElement 4 1) w13 w43
    [2, 1] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action39 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 1) (σ w43 v) = σ w41 v := by
  apply difference_step h (rootElement 3 1) w43 w41
    [2] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action40 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w01
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action41 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w01 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w01
    [1, 2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action42 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w02 v) = σ w04 v := by
  apply difference_step h (rootElement 2 4) w02 w04
    [] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action43 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w02 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w02
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action44 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w03
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action45 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w03 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w03
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action46 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w04
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action47 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w04 v) = σ w02 v := by
  apply difference_step h (rootElement 4 2) w04 w02
    [2] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action48 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w12 v) = σ w14 v := by
  apply difference_step h (rootElement 2 4) w12 w14
    [] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action49 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w12
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action50 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 1 3) (σ w14 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w14
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action51 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w13 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w13
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action52 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w13 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w13
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action53 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w14 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w14
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action54 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w14 v) = σ w12 v := by
  apply difference_step h (rootElement 4 2) w14 w12
    [2] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action55 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 3) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w04
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action56 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 3) (σ w14 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w14
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action57 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 2) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w12
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action58 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w23 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w23
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action59 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 2) (σ w23 v) = σ w43 v := by
  apply difference_step h (rootElement 4 2) w23 w43
    [2, 1] [2, 1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action60 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 2) (σ w43 v) = σ w42 v := by
  apply difference_step h (rootElement 3 2) w43 w42
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action61 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w04 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w04
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action62 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w04 v) = σ w03 v := by
  apply difference_step h (rootElement 4 3) w04 w03
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action63 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w12
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action64 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w12
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action65 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w13 v) = σ w14 v := by
  apply difference_step h (rootElement 3 4) w13 w14
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action66 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w13 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w13
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action67 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w14 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w14
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action68 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w14 v) = σ w13 v := by
  apply difference_step h (rootElement 4 3) w14 w13
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action69 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w23 v) = σ w24 v := by
  apply difference_step h (rootElement 3 4) w23 w24
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action70 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w23 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w23
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action71 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 2 4) (σ w24 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w24
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action72 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 3 4) (σ w24 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w24
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action73 (h : LocalHighestVector σ {0, 3} v) :
    difference σ (rootElement 4 3) (σ w24 v) = σ w23 v := by
  apply difference_step h (rootElement 4 3) w24 w23
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private def representatives : Fin 9 → SL5TenDimensional.Group :=
  ![w01, w02, w03, w04, w12, w13, w14, w23, w24]

private def vectors (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (T : V →ₗ[ZMod 2] V) (v : V) (i : Fin 9) : V :=
  σ (representatives i) v + T (σ (representatives i) v)

private def extractors (σ : Representation (ZMod 2) SL5TenDimensional.Group V) :
    Fin 9 → V →ₗ[ZMod 2] V :=
  ![(difference σ (rootElement 0 2)).comp (LinearMap.id),
    (difference σ (rootElement 2 3)).comp (LinearMap.id),
    (difference σ (rootElement 3 4)).comp (LinearMap.id),
    (difference σ (rootElement 0 2)).comp ((difference σ (rootElement 1 4)).comp (LinearMap.id)),
    (difference σ (rootElement 1 2)).comp ((difference σ (rootElement 1 3)).comp (LinearMap.id)),
    (difference σ (rootElement 1 3)).comp ((difference σ (rootElement 1 4)).comp (LinearMap.id)),
    (difference σ (rootElement 1 3)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 2 3)).comp ((difference σ (rootElement 2 4)).comp (LinearMap.id)),
    (difference σ (rootElement 2 4)).comp ((difference σ (rootElement 3 4)).comp (LinearMap.id))]

private theorem independent (h : LocalHighestVector σ {0, 3} v) (hv : v ≠ 0)
    (T : V →ₗ[ZMod 2] V) (hinj : Function.Injective T)
    (htranspose : ∀ (a b : Fin 5) (x : V),
      difference σ (rootElement a b) (T x) = T (difference σ (rootElement b a) x)) :
    LinearIndependent (ZMod 2) (vectors σ T v) := by
  apply linearIndependent_of_triangular _ (extractors σ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference σ (rootElement 2 3) (σ w01 v + T (σ w01 v)) = 0
      simp only [map_add, htranspose, action2 h, action3 h, map_zero, add_zero]
    · change difference σ (rootElement 3 4) (σ w01 v + T (σ w01 v)) = 0
      simp only [map_add, htranspose, action6 h, action7 h, map_zero, add_zero]
    · change difference σ (rootElement 3 4) (σ w02 v + T (σ w02 v)) = 0
      simp only [map_add, htranspose, action8 h, action9 h, map_zero, add_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 1 4) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action12 h, action13 h, action14 h, map_zero, add_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 1 4) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action15 h, action16 h, map_zero, add_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 1 4) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action17 h, action18 h, map_zero, add_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action21 h, action22 h, action23 h, map_zero, add_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action24 h, action25 h, map_zero, add_zero]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action26 h, action27 h, action28 h, map_zero, zero_add]
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (σ w04 v + T (σ w04 v))) = 0
      simp only [map_add, htranspose, action29 h, action30 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action12 h, action13 h, action29 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action15 h, action16 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action17 h, action18 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w04 v + T (σ w04 v))) = 0
      simp only [map_add, htranspose, action19 h, action20 h, action22 h, map_zero, zero_add]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w12 v + T (σ w12 v))) = 0
      simp only [map_add, htranspose, action34 h, action35 h, action36 h, map_zero, zero_add]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action40 h, action41 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action42 h, action43 h, action29 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action44 h, action45 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w04 v + T (σ w04 v))) = 0
      simp only [map_add, htranspose, action46 h, action47 h, action25 h, map_zero, zero_add]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w12 v + T (σ w12 v))) = 0
      simp only [map_add, htranspose, action48 h, action49 h, action50 h, map_zero, add_zero]
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w13 v + T (σ w13 v))) = 0
      simp only [map_add, htranspose, action51 h, action52 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action40 h, action41 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action42 h, action43 h, action55 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action44 h, action45 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w04 v + T (σ w04 v))) = 0
      simp only [map_add, htranspose, action46 h, action47 h, action5 h, map_zero, zero_add]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w12 v + T (σ w12 v))) = 0
      simp only [map_add, htranspose, action48 h, action49 h, action56 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w13 v + T (σ w13 v))) = 0
      simp only [map_add, htranspose, action51 h, action52 h, map_zero, add_zero]
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w14 v + T (σ w14 v))) = 0
      simp only [map_add, htranspose, action53 h, action54 h, action57 h, map_zero, zero_add]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w01 v + T (σ w01 v))) = 0
      simp only [map_add, htranspose, action6 h, action7 h, map_zero, add_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w02 v + T (σ w02 v))) = 0
      simp only [map_add, htranspose, action8 h, action9 h, map_zero, add_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w03 v + T (σ w03 v))) = 0
      simp only [map_add, htranspose, action10 h, action11 h, action46 h, map_zero, add_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w04 v + T (σ w04 v))) = 0
      simp only [map_add, htranspose, action61 h, action62 h, action45 h, map_zero, zero_add]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w12 v + T (σ w12 v))) = 0
      simp only [map_add, htranspose, action63 h, action64 h, map_zero, add_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w13 v + T (σ w13 v))) = 0
      simp only [map_add, htranspose, action65 h, action66 h, action53 h, map_zero, add_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w14 v + T (σ w14 v))) = 0
      simp only [map_add, htranspose, action67 h, action68 h, action52 h, map_zero, zero_add]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w23 v + T (σ w23 v))) = 0
      simp only [map_add, htranspose, action69 h, action70 h, action71 h, map_zero, add_zero]
  · intro i
    fin_cases i
    · change difference σ (rootElement 0 2) (σ w01 v + T (σ w01 v)) ≠ 0
      simp only [map_add, htranspose, action0 h, action1 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w21 hv)
    · change difference σ (rootElement 2 3) (σ w02 v + T (σ w02 v)) ≠ 0
      simp only [map_add, htranspose, action4 h, action5 h, map_zero, add_zero]
      exact translate_ne_zero σ _ hv
    · change difference σ (rootElement 3 4) (σ w03 v + T (σ w03 v)) ≠ 0
      simp only [map_add, htranspose, action10 h, action11 h, map_zero, add_zero]
      exact translate_ne_zero σ _ hv
    · change difference σ (rootElement 0 2) (difference σ (rootElement 1 4) (σ w04 v + T (σ w04 v))) ≠ 0
      simp only [map_add, htranspose, action19 h, action20 h, action1 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w21 hv)
    · change difference σ (rootElement 1 2) (difference σ (rootElement 1 3) (σ w12 v + T (σ w12 v))) ≠ 0
      simp only [map_add, htranspose, action31 h, action32 h, action33 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w31 hv)
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 4) (σ w13 v + T (σ w13 v))) ≠ 0
      simp only [map_add, htranspose, action37 h, action38 h, action39 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w41 hv)
    · change difference σ (rootElement 1 3) (difference σ (rootElement 2 4) (σ w14 v + T (σ w14 v))) ≠ 0
      simp only [map_add, htranspose, action53 h, action54 h, action32 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w32 hv)
    · change difference σ (rootElement 2 3) (difference σ (rootElement 2 4) (σ w23 v + T (σ w23 v))) ≠ 0
      simp only [map_add, htranspose, action58 h, action59 h, action60 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w42 hv)
    · change difference σ (rootElement 2 4) (difference σ (rootElement 3 4) (σ w24 v + T (σ w24 v))) ≠ 0
      simp only [map_add, htranspose, action72 h, action73 h, action59 h, zero_add]
      simpa only [map_zero] using
        hinj.ne
          (translate_ne_zero σ w43 hv)

/-- Nine independent moved vectors give a lower bound on the displacement rank.
Only the literal root-intertwining equations and injectivity of the operator are used. -/
theorem nine_le_displacement_rank [FiniteDimensional (ZMod 2) V]
    (h : LocalHighestVector σ {0, 3} v) (hv : v ≠ 0)
    (T : V →ₗ[ZMod 2] V) (hinj : Function.Injective T)
    (htranspose : ∀ (a b : Fin 5) (x : V),
      difference σ (rootElement a b) (T x) = T (difference σ (rootElement b a) x)) :
    9 ≤ Module.finrank (ZMod 2) (LinearMap.range (T - LinearMap.id)) := by
  let D := T - LinearMap.id
  have hmem (i : Fin 9) : vectors σ T v i ∈ LinearMap.range D := by
    refine ⟨σ (representatives i) v, ?_⟩
    change T (σ (representatives i) v) - σ (representatives i) v =
      σ (representatives i) v + T (σ (representatives i) v)
    rw [ZModModule.sub_eq_add, add_comm]
  let f : Fin 9 → LinearMap.range D := fun i => ⟨vectors σ T v i, hmem i⟩
  have hi : LinearIndependent (ZMod 2) f :=
    LinearIndependent.of_comp (LinearMap.range D).subtype (independent h hv T hinj htranspose)
  simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Endpoint
