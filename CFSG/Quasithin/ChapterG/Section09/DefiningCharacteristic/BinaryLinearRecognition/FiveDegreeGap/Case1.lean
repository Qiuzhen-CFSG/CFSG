module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Basic
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Endpoints

/-!
# Dimension certificate for highest-vector support `{1}`

The permutation translates below are linearly independent: each transvection
extractor kills its predecessors and maps its own vector to a nonzero translate.
The finite matrix equalities are checked by kernel reduction using the local
highest-vector relations. No torus weight separation or absolute irreducibility
is assumed. Singleton middle supports also have their entire permutation span
stable under every transvection, yielding the exact dimension by irreducibility.

This extends the extraction method in `Support.Multiple.Separated` to the degree
gap in Aschbacher--Smith, G.9.3(13), printed pp.354,356–357/PDF pp.365,367–368.
-/

@[expose] public section

open Representation Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case1
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {1} v)
include h

private def w0 : Group := swapWord []
private def w1 : Group := swapWord [1]
private def w2 : Group := swapWord [0, 1]
private def w3 : Group := swapWord [2, 1]
private def w4 : Group := swapWord [2, 0, 1]
private def w5 : Group := swapWord [3, 2, 1]
private def w6 : Group := swapWord [3, 2, 0, 1]
private def w7 : Group := swapWord [1, 2, 0, 1]
private def w8 : Group := swapWord [3, 1, 2, 0, 1]
private def w9 : Group := swapWord [2, 3, 1, 2, 0, 1]
private theorem action0 : difference ρ (rootElement 1 0) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w0
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action1 : difference ρ (rootElement 1 0) (ρ w1 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 0) w1 w2
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action2 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action3 : difference ρ (rootElement 0 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action4 : difference ρ (rootElement 0 1) (ρ w2 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 1) w2 w1
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action5 : difference ρ (rootElement 1 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w0
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action6 : difference ρ (rootElement 1 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w1
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action7 : difference ρ (rootElement 1 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action8 : difference ρ (rootElement 1 3) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 3) w3 w0
    [] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action9 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action10 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action11 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action12 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action13 : difference ρ (rootElement 0 3) (ρ w4 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 3) w4 w0
    [] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action14 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action15 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action16 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action17 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action18 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action19 : difference ρ (rootElement 1 4) (ρ w5 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 4) w5 w0
    [] [3, 2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action20 : difference ρ (rootElement 0 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w0
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action21 : difference ρ (rootElement 0 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w1
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action22 : difference ρ (rootElement 0 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action23 : difference ρ (rootElement 0 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w3
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action24 : difference ρ (rootElement 0 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w4
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action25 : difference ρ (rootElement 0 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action26 : difference ρ (rootElement 0 4) (ρ w6 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 4) w6 w0
    [] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action27 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action28 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action29 : difference ρ (rootElement 0 2) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 2) w2 w0
    [] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action30 : difference ρ (rootElement 0 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w3
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action31 : difference ρ (rootElement 0 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w4
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action32 : difference ρ (rootElement 0 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action33 : difference ρ (rootElement 0 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w6
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action34 : difference ρ (rootElement 0 2) (ρ w7 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 2) w7 w3
    [0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action35 : difference ρ (rootElement 1 0) (ρ w3 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 0) w3 w4
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action36 : difference ρ (rootElement 0 2) (ρ w8 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 2) w8 w5
    [0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action37 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action38 : difference ρ (rootElement 0 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w6
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action39 : difference ρ (rootElement 0 3) (ρ w7 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 3) w7 w1
    [] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action40 : difference ρ (rootElement 0 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w8
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action41 : difference ρ (rootElement 0 3) (ρ w9 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 3) w9 w5
    [0] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action42 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action43 : difference ρ (rootElement 2 0) (ρ w0 v) = ρ w2 v := by
  apply difference_step h (rootElement 2 0) w0 w2
    [0] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action44 : difference ρ (rootElement 2 1) (ρ w0 v) = ρ w1 v := by
  apply difference_step h (rootElement 2 1) w0 w1
    [] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action45 : difference ρ (rootElement 2 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w0
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action46 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action47 : difference ρ (rootElement 3 0) (ρ w0 v) = ρ w4 v := by
  apply difference_step h (rootElement 3 0) w0 w4
    [2, 0] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action48 : difference ρ (rootElement 3 1) (ρ w0 v) = ρ w3 v := by
  apply difference_step h (rootElement 3 1) w0 w3
    [2] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action49 : difference ρ (rootElement 3 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w0
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action50 : difference ρ (rootElement 3 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w0
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action51 : difference ρ (rootElement 4 0) (ρ w0 v) = ρ w6 v := by
  apply difference_step h (rootElement 4 0) w0 w6
    [3, 2, 3, 0] [3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action52 : difference ρ (rootElement 4 1) (ρ w0 v) = ρ w5 v := by
  apply difference_step h (rootElement 4 1) w0 w5
    [3, 2, 3] [3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action53 : difference ρ (rootElement 4 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w0
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action54 : difference ρ (rootElement 4 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w0
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action55 : difference ρ (rootElement 1 2) (ρ w1 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 2) w1 w0
    [] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action56 : difference ρ (rootElement 2 0) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w1
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action57 : difference ρ (rootElement 2 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w1
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action58 : difference ρ (rootElement 2 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w1
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action59 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action60 : difference ρ (rootElement 3 0) (ρ w1 v) = ρ w7 v := by
  apply difference_step h (rootElement 3 0) w1 w7
    [2, 0] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action61 : difference ρ (rootElement 3 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w1
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action62 : difference ρ (rootElement 3 2) (ρ w1 v) = ρ w3 v := by
  apply difference_step h (rootElement 3 2) w1 w3
    [2] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action63 : difference ρ (rootElement 3 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w1
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action64 : difference ρ (rootElement 4 0) (ρ w1 v) = ρ w8 v := by
  apply difference_step h (rootElement 4 0) w1 w8
    [3, 2, 3, 0] [3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action65 : difference ρ (rootElement 4 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w1
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action66 : difference ρ (rootElement 4 2) (ρ w1 v) = ρ w5 v := by
  apply difference_step h (rootElement 4 2) w1 w5
    [3, 2, 3] [2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action67 : difference ρ (rootElement 4 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w1
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action68 : difference ρ (rootElement 1 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w2
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action69 : difference ρ (rootElement 1 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w2
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action70 : difference ρ (rootElement 2 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w2
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action71 : difference ρ (rootElement 2 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w2
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action72 : difference ρ (rootElement 2 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w2
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action73 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action74 : difference ρ (rootElement 3 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w2
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action75 : difference ρ (rootElement 3 1) (ρ w2 v) = ρ w7 v := by
  apply difference_step h (rootElement 3 1) w2 w7
    [2, 0] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action76 : difference ρ (rootElement 3 2) (ρ w2 v) = ρ w4 v := by
  apply difference_step h (rootElement 3 2) w2 w4
    [2] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action77 : difference ρ (rootElement 3 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w2
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action78 : difference ρ (rootElement 4 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w2
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action79 : difference ρ (rootElement 4 1) (ρ w2 v) = ρ w8 v := by
  apply difference_step h (rootElement 4 1) w2 w8
    [3, 2, 3, 0] [2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action80 : difference ρ (rootElement 4 2) (ρ w2 v) = ρ w6 v := by
  apply difference_step h (rootElement 4 2) w2 w6
    [3, 2, 3] [2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action81 : difference ρ (rootElement 4 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w2
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action82 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action83 : difference ρ (rootElement 1 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w3
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action84 : difference ρ (rootElement 2 0) (ρ w3 v) = ρ w7 v := by
  apply difference_step h (rootElement 2 0) w3 w7
    [2, 0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action85 : difference ρ (rootElement 2 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w3
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action86 : difference ρ (rootElement 2 3) (ρ w3 v) = ρ w1 v := by
  apply difference_step h (rootElement 2 3) w3 w1
    [2] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action87 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action88 : difference ρ (rootElement 3 0) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w3
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action89 : difference ρ (rootElement 3 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w3
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action90 : difference ρ (rootElement 3 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w3
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action91 : difference ρ (rootElement 3 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w3
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action92 : difference ρ (rootElement 4 0) (ρ w3 v) = ρ w9 v := by
  apply difference_step h (rootElement 4 0) w3 w9
    [3, 2, 3, 0] [3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action93 : difference ρ (rootElement 4 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w3
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action94 : difference ρ (rootElement 4 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w3
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action95 : difference ρ (rootElement 4 3) (ρ w3 v) = ρ w5 v := by
  apply difference_step h (rootElement 4 3) w3 w5
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action96 : difference ρ (rootElement 0 1) (ρ w4 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 1) w4 w3
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action97 : difference ρ (rootElement 1 0) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w4
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action98 : difference ρ (rootElement 1 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w4
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action99 : difference ρ (rootElement 1 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w4
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action100 : difference ρ (rootElement 2 0) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w4
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action101 : difference ρ (rootElement 2 1) (ρ w4 v) = ρ w7 v := by
  apply difference_step h (rootElement 2 1) w4 w7
    [2, 0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action102 : difference ρ (rootElement 2 3) (ρ w4 v) = ρ w2 v := by
  apply difference_step h (rootElement 2 3) w4 w2
    [2] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action103 : difference ρ (rootElement 2 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w4
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action104 : difference ρ (rootElement 3 0) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w4
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action105 : difference ρ (rootElement 3 1) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w4
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action106 : difference ρ (rootElement 3 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w4
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action107 : difference ρ (rootElement 3 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w4
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action108 : difference ρ (rootElement 4 0) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w4
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action109 : difference ρ (rootElement 4 1) (ρ w4 v) = ρ w9 v := by
  apply difference_step h (rootElement 4 1) w4 w9
    [3, 2, 3, 0] [2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action110 : difference ρ (rootElement 4 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w4
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action111 : difference ρ (rootElement 4 3) (ρ w4 v) = ρ w6 v := by
  apply difference_step h (rootElement 4 3) w4 w6
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action112 : difference ρ (rootElement 0 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w5
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action113 : difference ρ (rootElement 1 0) (ρ w5 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 0) w5 w6
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action114 : difference ρ (rootElement 1 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w5
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action115 : difference ρ (rootElement 1 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w5
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action116 : difference ρ (rootElement 2 0) (ρ w5 v) = ρ w8 v := by
  apply difference_step h (rootElement 2 0) w5 w8
    [2, 0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action117 : difference ρ (rootElement 2 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w5
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action118 : difference ρ (rootElement 2 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w5
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action119 : difference ρ (rootElement 2 4) (ρ w5 v) = ρ w1 v := by
  apply difference_step h (rootElement 2 4) w5 w1
    [2] [3, 2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action120 : difference ρ (rootElement 3 0) (ρ w5 v) = ρ w9 v := by
  apply difference_step h (rootElement 3 0) w5 w9
    [3, 2, 3, 0] [3, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action121 : difference ρ (rootElement 3 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w5
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action122 : difference ρ (rootElement 3 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w5
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action123 : difference ρ (rootElement 3 4) (ρ w5 v) = ρ w3 v := by
  apply difference_step h (rootElement 3 4) w5 w3
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action124 : difference ρ (rootElement 4 0) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w5
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action125 : difference ρ (rootElement 4 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w5
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action126 : difference ρ (rootElement 4 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w5
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action127 : difference ρ (rootElement 4 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w5
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action128 : difference ρ (rootElement 0 1) (ρ w6 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 1) w6 w5
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action129 : difference ρ (rootElement 1 0) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w6
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action130 : difference ρ (rootElement 1 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w6
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action131 : difference ρ (rootElement 1 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w6
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action132 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action133 : difference ρ (rootElement 2 0) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w6
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action134 : difference ρ (rootElement 2 1) (ρ w6 v) = ρ w8 v := by
  apply difference_step h (rootElement 2 1) w6 w8
    [2, 0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action135 : difference ρ (rootElement 2 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w6
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action136 : difference ρ (rootElement 2 4) (ρ w6 v) = ρ w2 v := by
  apply difference_step h (rootElement 2 4) w6 w2
    [2] [3, 2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action137 : difference ρ (rootElement 3 0) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w6
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action138 : difference ρ (rootElement 3 1) (ρ w6 v) = ρ w9 v := by
  apply difference_step h (rootElement 3 1) w6 w9
    [3, 2, 3, 0] [2, 3, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action139 : difference ρ (rootElement 3 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w6
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action140 : difference ρ (rootElement 3 4) (ρ w6 v) = ρ w4 v := by
  apply difference_step h (rootElement 3 4) w6 w4
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action141 : difference ρ (rootElement 4 0) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w6
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action142 : difference ρ (rootElement 4 1) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w6
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action143 : difference ρ (rootElement 4 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w6
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action144 : difference ρ (rootElement 4 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w6
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action145 : difference ρ (rootElement 0 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w7
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action146 : difference ρ (rootElement 0 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w7
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action147 : difference ρ (rootElement 1 0) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w7
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action148 : difference ρ (rootElement 1 2) (ρ w7 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 2) w7 w4
    [2, 0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action149 : difference ρ (rootElement 1 3) (ρ w7 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 3) w7 w2
    [2] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action150 : difference ρ (rootElement 1 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w7
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action151 : difference ρ (rootElement 2 0) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w7
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action152 : difference ρ (rootElement 2 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w7
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action153 : difference ρ (rootElement 2 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w7
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action154 : difference ρ (rootElement 2 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w7
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action155 : difference ρ (rootElement 3 0) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w7
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action156 : difference ρ (rootElement 3 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w7
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action157 : difference ρ (rootElement 3 2) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w7
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action158 : difference ρ (rootElement 3 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w7
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action159 : difference ρ (rootElement 4 0) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w7
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action160 : difference ρ (rootElement 4 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w7
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action161 : difference ρ (rootElement 4 2) (ρ w7 v) = ρ w9 v := by
  apply difference_step h (rootElement 4 2) w7 w9
    [3, 2, 3, 0] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action162 : difference ρ (rootElement 4 3) (ρ w7 v) = ρ w8 v := by
  apply difference_step h (rootElement 4 3) w7 w8
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action163 : difference ρ (rootElement 0 1) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w8
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action164 : difference ρ (rootElement 0 4) (ρ w8 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 4) w8 w1
    [] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action165 : difference ρ (rootElement 1 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w8
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action166 : difference ρ (rootElement 1 2) (ρ w8 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 2) w8 w6
    [2, 0] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action167 : difference ρ (rootElement 1 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w8
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action168 : difference ρ (rootElement 1 4) (ρ w8 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 4) w8 w2
    [2] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action169 : difference ρ (rootElement 2 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w8
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action170 : difference ρ (rootElement 2 1) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w8
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action171 : difference ρ (rootElement 2 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w8
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action172 : difference ρ (rootElement 2 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w8
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action173 : difference ρ (rootElement 3 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w8
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action174 : difference ρ (rootElement 3 1) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w8
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action175 : difference ρ (rootElement 3 2) (ρ w8 v) = ρ w9 v := by
  apply difference_step h (rootElement 3 2) w8 w9
    [3, 2, 3, 0] [3, 2, 3, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action176 : difference ρ (rootElement 3 4) (ρ w8 v) = ρ w7 v := by
  apply difference_step h (rootElement 3 4) w8 w7
    [3, 2, 3] [3, 2, 3] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action177 : difference ρ (rootElement 4 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w8
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action178 : difference ρ (rootElement 4 1) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w8
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action179 : difference ρ (rootElement 4 2) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w8
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action180 : difference ρ (rootElement 4 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w8
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action181 : difference ρ (rootElement 0 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w9
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action182 : difference ρ (rootElement 0 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w9
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action183 : difference ρ (rootElement 0 4) (ρ w9 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 4) w9 w3
    [] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action184 : difference ρ (rootElement 1 0) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w9
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action185 : difference ρ (rootElement 1 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w9
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action186 : difference ρ (rootElement 1 3) (ρ w9 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 3) w9 w6
    [2, 0] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action187 : difference ρ (rootElement 1 4) (ρ w9 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 4) w9 w4
    [2] [3, 2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action188 : difference ρ (rootElement 2 0) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w9
    [3, 2, 3] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action189 : difference ρ (rootElement 2 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w9
    [3] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action190 : difference ρ (rootElement 2 3) (ρ w9 v) = ρ w8 v := by
  apply difference_step h (rootElement 2 3) w9 w8
    [3, 2, 3, 0] [3, 2, 3, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action191 : difference ρ (rootElement 2 4) (ρ w9 v) = ρ w7 v := by
  apply difference_step h (rootElement 2 4) w9 w7
    [3, 2, 3] [3, 2, 3, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action192 : difference ρ (rootElement 3 0) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w9
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action193 : difference ρ (rootElement 3 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w9
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action194 : difference ρ (rootElement 3 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 3 2) w9
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action195 : difference ρ (rootElement 3 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w9
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action196 : difference ρ (rootElement 4 0) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 4 0) w9
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action197 : difference ρ (rootElement 4 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w9
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action198 : difference ρ (rootElement 4 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 4 2) w9
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action199 : difference ρ (rootElement 4 3) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 4 3) w9
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 10 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 10 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 1 0)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 4)).comp (LinearMap.id),
    (difference ρ (rootElement 1 0)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id))]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference ρ (rootElement 1 0) (ρ w0 v) = 0
      rw [action0 h]
    · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
      rw [action2 h]
    · change difference ρ (rootElement 0 1) (ρ w1 v) = 0
      rw [action3 h]
    · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
      rw [action5 h]
    · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
      rw [action6 h]
    · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
      rw [action7 h]
    · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
      rw [action9 h]
    · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
      rw [action10 h]
    · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
      rw [action11 h]
    · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
      rw [action12 h]
    · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
      rw [action14 h]
    · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
      rw [action15 h]
    · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
      rw [action16 h]
    · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
      rw [action17 h]
    · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
      rw [action18 h]
    · change difference ρ (rootElement 0 4) (ρ w0 v) = 0
      rw [action20 h]
    · change difference ρ (rootElement 0 4) (ρ w1 v) = 0
      rw [action21 h]
    · change difference ρ (rootElement 0 4) (ρ w2 v) = 0
      rw [action22 h]
    · change difference ρ (rootElement 0 4) (ρ w3 v) = 0
      rw [action23 h]
    · change difference ρ (rootElement 0 4) (ρ w4 v) = 0
      rw [action24 h]
    · change difference ρ (rootElement 0 4) (ρ w5 v) = 0
      rw [action25 h]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
      rw [action27 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
      rw [action29 h, action0 h]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
      rw [action30 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
      rw [action31 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
      rw [action32 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
      rw [action33 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
      rw [action27 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
      rw [action29 h, action14 h]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
      rw [action30 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
      rw [action31 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
      rw [action32 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
      rw [action33 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w7 v)) = 0
      rw [action34 h, action17 h]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
      rw [action9 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
      rw [action10 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
      rw [action11 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
      rw [action12 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
      rw [action13 h, action14 h]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
      rw [action37 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
      rw [action38 h, map_zero]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
      rw [action39 h, action15 h]
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
      rw [action40 h, map_zero]
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w5 v) ≠ 0
      rw [action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (ρ w6 v) ≠ 0
      rw [action26 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 2) (ρ w7 v)) ≠ 0
      rw [action34 h, action35 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 2) (ρ w8 v)) ≠ 0
      rw [action36 h, action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w9 v)) ≠ 0
      rw [action41 h, action19 h]
      exact translate_ne_zero ρ _ hv

theorem degree_le [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    10 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank
private theorem spanning [IsIrreducible ρ] (hv : v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range (vectors ρ v)) = ⊤ := by
  apply span_eq_top_of_root_differences (ρ := ρ) (vectors ρ v) 0 (translate_ne_zero ρ _ hv)
  intro a b hab i
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases i
  · change difference ρ (rootElement 0 1) (ρ w0 v) ∈ _
    rw [action2 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w1 v) ∈ _
    rw [action3 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w2 v) ∈ _
    rw [action4 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 0 1) (ρ w3 v) ∈ _
    rw [action82 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w4 v) ∈ _
    rw [action96 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 0 1) (ρ w5 v) ∈ _
    rw [action112 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w6 v) ∈ _
    rw [action128 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 0 1) (ρ w7 v) ∈ _
    rw [action145 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w8 v) ∈ _
    rw [action163 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 1) (ρ w9 v) ∈ _
    rw [action181 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w0 v) ∈ _
    rw [action27 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w1 v) ∈ _
    rw [action28 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w2 v) ∈ _
    rw [action29 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 0 2) (ρ w3 v) ∈ _
    rw [action30 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w4 v) ∈ _
    rw [action31 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w5 v) ∈ _
    rw [action32 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w6 v) ∈ _
    rw [action33 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 2) (ρ w7 v) ∈ _
    rw [action34 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 0 2) (ρ w8 v) ∈ _
    rw [action36 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 0 2) (ρ w9 v) ∈ _
    rw [action182 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w0 v) ∈ _
    rw [action9 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w1 v) ∈ _
    rw [action10 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w2 v) ∈ _
    rw [action11 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w3 v) ∈ _
    rw [action12 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w4 v) ∈ _
    rw [action13 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 0 3) (ρ w5 v) ∈ _
    rw [action37 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w6 v) ∈ _
    rw [action38 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w7 v) ∈ _
    rw [action39 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 0 3) (ρ w8 v) ∈ _
    rw [action40 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 3) (ρ w9 v) ∈ _
    rw [action41 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 0 4) (ρ w0 v) ∈ _
    rw [action20 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w1 v) ∈ _
    rw [action21 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w2 v) ∈ _
    rw [action22 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w3 v) ∈ _
    rw [action23 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w4 v) ∈ _
    rw [action24 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w5 v) ∈ _
    rw [action25 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w6 v) ∈ _
    rw [action26 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 0 4) (ρ w7 v) ∈ _
    rw [action146 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 0 4) (ρ w8 v) ∈ _
    rw [action164 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 0 4) (ρ w9 v) ∈ _
    rw [action183 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 1 0) (ρ w0 v) ∈ _
    rw [action0 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w1 v) ∈ _
    rw [action1 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 1 0) (ρ w2 v) ∈ _
    rw [action68 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w3 v) ∈ _
    rw [action35 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 1 0) (ρ w4 v) ∈ _
    rw [action97 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w5 v) ∈ _
    rw [action113 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 1 0) (ρ w6 v) ∈ _
    rw [action129 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w7 v) ∈ _
    rw [action147 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w8 v) ∈ _
    rw [action165 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 0) (ρ w9 v) ∈ _
    rw [action184 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w0 v) ∈ _
    rw [action42 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w1 v) ∈ _
    rw [action55 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 1 2) (ρ w2 v) ∈ _
    rw [action69 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w3 v) ∈ _
    rw [action83 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w4 v) ∈ _
    rw [action98 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w5 v) ∈ _
    rw [action114 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w6 v) ∈ _
    rw [action130 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 2) (ρ w7 v) ∈ _
    rw [action148 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 1 2) (ρ w8 v) ∈ _
    rw [action166 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 1 2) (ρ w9 v) ∈ _
    rw [action185 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w0 v) ∈ _
    rw [action5 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w1 v) ∈ _
    rw [action6 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w2 v) ∈ _
    rw [action7 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w3 v) ∈ _
    rw [action8 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 1 3) (ρ w4 v) ∈ _
    rw [action99 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w5 v) ∈ _
    rw [action115 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w6 v) ∈ _
    rw [action131 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w7 v) ∈ _
    rw [action149 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 1 3) (ρ w8 v) ∈ _
    rw [action167 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 3) (ρ w9 v) ∈ _
    rw [action186 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 1 4) (ρ w0 v) ∈ _
    rw [action14 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w1 v) ∈ _
    rw [action15 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w2 v) ∈ _
    rw [action16 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w3 v) ∈ _
    rw [action17 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w4 v) ∈ _
    rw [action18 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w5 v) ∈ _
    rw [action19 h]
    exact Submodule.subset_span ⟨0, rfl⟩
  · change difference ρ (rootElement 1 4) (ρ w6 v) ∈ _
    rw [action132 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w7 v) ∈ _
    rw [action150 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 1 4) (ρ w8 v) ∈ _
    rw [action168 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 1 4) (ρ w9 v) ∈ _
    rw [action187 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 2 0) (ρ w0 v) ∈ _
    rw [action43 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 2 0) (ρ w1 v) ∈ _
    rw [action56 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w2 v) ∈ _
    rw [action70 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w3 v) ∈ _
    rw [action84 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 2 0) (ρ w4 v) ∈ _
    rw [action100 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w5 v) ∈ _
    rw [action116 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 2 0) (ρ w6 v) ∈ _
    rw [action133 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w7 v) ∈ _
    rw [action151 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w8 v) ∈ _
    rw [action169 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 0) (ρ w9 v) ∈ _
    rw [action188 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w0 v) ∈ _
    rw [action44 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 2 1) (ρ w1 v) ∈ _
    rw [action57 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w2 v) ∈ _
    rw [action71 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w3 v) ∈ _
    rw [action85 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w4 v) ∈ _
    rw [action101 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 2 1) (ρ w5 v) ∈ _
    rw [action117 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w6 v) ∈ _
    rw [action134 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 2 1) (ρ w7 v) ∈ _
    rw [action152 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w8 v) ∈ _
    rw [action170 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 1) (ρ w9 v) ∈ _
    rw [action189 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w0 v) ∈ _
    rw [action45 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w1 v) ∈ _
    rw [action58 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w2 v) ∈ _
    rw [action72 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w3 v) ∈ _
    rw [action86 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 2 3) (ρ w4 v) ∈ _
    rw [action102 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 2 3) (ρ w5 v) ∈ _
    rw [action118 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w6 v) ∈ _
    rw [action135 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w7 v) ∈ _
    rw [action153 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w8 v) ∈ _
    rw [action171 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 3) (ρ w9 v) ∈ _
    rw [action190 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 2 4) (ρ w0 v) ∈ _
    rw [action46 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w1 v) ∈ _
    rw [action59 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w2 v) ∈ _
    rw [action73 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w3 v) ∈ _
    rw [action87 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w4 v) ∈ _
    rw [action103 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w5 v) ∈ _
    rw [action119 h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change difference ρ (rootElement 2 4) (ρ w6 v) ∈ _
    rw [action136 h]
    exact Submodule.subset_span ⟨2, rfl⟩
  · change difference ρ (rootElement 2 4) (ρ w7 v) ∈ _
    rw [action154 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w8 v) ∈ _
    rw [action172 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 2 4) (ρ w9 v) ∈ _
    rw [action191 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 3 0) (ρ w0 v) ∈ _
    rw [action47 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 3 0) (ρ w1 v) ∈ _
    rw [action60 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 3 0) (ρ w2 v) ∈ _
    rw [action74 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w3 v) ∈ _
    rw [action88 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w4 v) ∈ _
    rw [action104 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w5 v) ∈ _
    rw [action120 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 3 0) (ρ w6 v) ∈ _
    rw [action137 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w7 v) ∈ _
    rw [action155 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w8 v) ∈ _
    rw [action173 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 0) (ρ w9 v) ∈ _
    rw [action192 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w0 v) ∈ _
    rw [action48 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 3 1) (ρ w1 v) ∈ _
    rw [action61 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w2 v) ∈ _
    rw [action75 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 3 1) (ρ w3 v) ∈ _
    rw [action89 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w4 v) ∈ _
    rw [action105 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w5 v) ∈ _
    rw [action121 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w6 v) ∈ _
    rw [action138 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 3 1) (ρ w7 v) ∈ _
    rw [action156 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w8 v) ∈ _
    rw [action174 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 1) (ρ w9 v) ∈ _
    rw [action193 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w0 v) ∈ _
    rw [action49 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w1 v) ∈ _
    rw [action62 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 3 2) (ρ w2 v) ∈ _
    rw [action76 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 3 2) (ρ w3 v) ∈ _
    rw [action90 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w4 v) ∈ _
    rw [action106 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w5 v) ∈ _
    rw [action122 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w6 v) ∈ _
    rw [action139 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w7 v) ∈ _
    rw [action157 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 2) (ρ w8 v) ∈ _
    rw [action175 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 3 2) (ρ w9 v) ∈ _
    rw [action194 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w0 v) ∈ _
    rw [action50 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w1 v) ∈ _
    rw [action63 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w2 v) ∈ _
    rw [action77 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w3 v) ∈ _
    rw [action91 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w4 v) ∈ _
    rw [action107 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w5 v) ∈ _
    rw [action123 h]
    exact Submodule.subset_span ⟨3, rfl⟩
  · change difference ρ (rootElement 3 4) (ρ w6 v) ∈ _
    rw [action140 h]
    exact Submodule.subset_span ⟨4, rfl⟩
  · change difference ρ (rootElement 3 4) (ρ w7 v) ∈ _
    rw [action158 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 3 4) (ρ w8 v) ∈ _
    rw [action176 h]
    exact Submodule.subset_span ⟨7, rfl⟩
  · change difference ρ (rootElement 3 4) (ρ w9 v) ∈ _
    rw [action195 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w0 v) ∈ _
    rw [action51 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 4 0) (ρ w1 v) ∈ _
    rw [action64 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 4 0) (ρ w2 v) ∈ _
    rw [action78 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w3 v) ∈ _
    rw [action92 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 4 0) (ρ w4 v) ∈ _
    rw [action108 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w5 v) ∈ _
    rw [action124 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w6 v) ∈ _
    rw [action141 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w7 v) ∈ _
    rw [action159 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w8 v) ∈ _
    rw [action177 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 0) (ρ w9 v) ∈ _
    rw [action196 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w0 v) ∈ _
    rw [action52 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 4 1) (ρ w1 v) ∈ _
    rw [action65 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w2 v) ∈ _
    rw [action79 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 4 1) (ρ w3 v) ∈ _
    rw [action93 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w4 v) ∈ _
    rw [action109 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 4 1) (ρ w5 v) ∈ _
    rw [action125 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w6 v) ∈ _
    rw [action142 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w7 v) ∈ _
    rw [action160 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w8 v) ∈ _
    rw [action178 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 1) (ρ w9 v) ∈ _
    rw [action197 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w0 v) ∈ _
    rw [action53 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w1 v) ∈ _
    rw [action66 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 4 2) (ρ w2 v) ∈ _
    rw [action80 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 4 2) (ρ w3 v) ∈ _
    rw [action94 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w4 v) ∈ _
    rw [action110 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w5 v) ∈ _
    rw [action126 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w6 v) ∈ _
    rw [action143 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w7 v) ∈ _
    rw [action161 h]
    exact Submodule.subset_span ⟨9, rfl⟩
  · change difference ρ (rootElement 4 2) (ρ w8 v) ∈ _
    rw [action179 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 2) (ρ w9 v) ∈ _
    rw [action198 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w0 v) ∈ _
    rw [action54 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w1 v) ∈ _
    rw [action67 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w2 v) ∈ _
    rw [action81 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w3 v) ∈ _
    rw [action95 h]
    exact Submodule.subset_span ⟨5, rfl⟩
  · change difference ρ (rootElement 4 3) (ρ w4 v) ∈ _
    rw [action111 h]
    exact Submodule.subset_span ⟨6, rfl⟩
  · change difference ρ (rootElement 4 3) (ρ w5 v) ∈ _
    rw [action127 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w6 v) ∈ _
    rw [action144 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w7 v) ∈ _
    rw [action162 h]
    exact Submodule.subset_span ⟨8, rfl⟩
  · change difference ρ (rootElement 4 3) (ρ w8 v) ∈ _
    rw [action180 h]
    exact Submodule.zero_mem _
  · change difference ρ (rootElement 4 3) (ρ w9 v) ∈ _
    rw [action199 h]
    exact Submodule.zero_mem _
theorem finrank_eq [Module.Finite (ZMod 2) V] [IsIrreducible ρ]
    (hv : v ≠ 0) : Module.finrank (ZMod 2) V = 10 := by
  apply le_antisymm _ (degree_le h hv)
  exact (finrank_le_of_span_eq_top (spanning h hv)).trans (by decide +kernel)
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case1
