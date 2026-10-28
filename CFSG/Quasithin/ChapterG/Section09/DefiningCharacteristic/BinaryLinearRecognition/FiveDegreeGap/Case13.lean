module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Basic
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Endpoints

/-!
# Dimension certificate for highest-vector support `{1, 3}`

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
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case13
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {1, 3} v)
include h

private def w0 : Group := swapWord []
private def w1 : Group := swapWord [1]
private def w2 : Group := swapWord [3]
private def w3 : Group := swapWord [2, 1]
private def w4 : Group := swapWord [2, 3]
private def w5 : Group := swapWord [0, 1]
private def w6 : Group := swapWord [3, 1]
private def w7 : Group := swapWord [3, 2, 1]
private def w8 : Group := swapWord [2, 0, 1]
private def w9 : Group := swapWord [2, 3, 1]
private def w10 : Group := swapWord [3, 0, 1]
private def w11 : Group := swapWord [1, 2, 3]
private def w12 : Group := swapWord [2, 3, 0, 1]
private def w13 : Group := swapWord [0, 1, 2, 3]
private def w14 : Group := swapWord [3, 2, 3, 1]
private def w15 : Group := swapWord [3, 2, 0, 1]
private def w16 : Group := swapWord [2, 0, 1, 2, 3]
private def w17 : Group := swapWord [2, 1, 2, 3]
private theorem action0 : difference ρ (rootElement 1 0) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w0
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action1 : difference ρ (rootElement 1 0) (ρ w1 v) = ρ w5 v := by
  apply difference_step h (rootElement 1 0) w1 w5
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action2 : difference ρ (rootElement 3 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w0
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action3 : difference ρ (rootElement 3 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w1
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action4 : difference ρ (rootElement 3 4) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 3 4) w2 w0
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

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
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action8 : difference ρ (rootElement 1 3) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 3) w3 w0
    [] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action9 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action10 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action11 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action12 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action13 : difference ρ (rootElement 2 4) (ρ w4 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 4) w4 w0
    [] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action14 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action15 : difference ρ (rootElement 0 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action16 : difference ρ (rootElement 0 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action17 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action18 : difference ρ (rootElement 0 1) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w4
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action19 : difference ρ (rootElement 0 1) (ρ w5 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 1) w5 w1
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action20 : difference ρ (rootElement 3 0) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w5
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action21 : difference ρ (rootElement 1 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w2
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action22 : difference ρ (rootElement 1 0) (ρ w3 v) = ρ w8 v := by
  apply difference_step h (rootElement 1 0) w3 w8
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action23 : difference ρ (rootElement 3 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w8
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action24 : difference ρ (rootElement 1 0) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w4
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action25 : difference ρ (rootElement 1 0) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w5
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action26 : difference ρ (rootElement 1 0) (ρ w6 v) = ρ w10 v := by
  apply difference_step h (rootElement 1 0) w6 w10
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action27 : difference ρ (rootElement 3 0) (ρ w10 v) = ρ w13 v := by
  apply difference_step h (rootElement 3 0) w10 w13
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action28 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action29 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action30 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action31 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action32 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action33 : difference ρ (rootElement 1 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action34 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action35 : difference ρ (rootElement 1 4) (ρ w7 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 4) w7 w2
    [] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action36 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action37 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action38 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action39 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action40 : difference ρ (rootElement 0 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w4
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action41 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action42 : difference ρ (rootElement 0 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w6
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action43 : difference ρ (rootElement 0 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w7
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action44 : difference ρ (rootElement 0 3) (ρ w8 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 3) w8 w0
    [] [2, 0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action45 : difference ρ (rootElement 2 0) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w5
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action46 : difference ρ (rootElement 2 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w8
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action47 : difference ρ (rootElement 2 0) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w10
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action48 : difference ρ (rootElement 1 0) (ρ w7 v) = ρ w15 v := by
  apply difference_step h (rootElement 1 0) w7 w15
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action49 : difference ρ (rootElement 2 0) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w15
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action50 : difference ρ (rootElement 1 0) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w8
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action51 : difference ρ (rootElement 1 0) (ρ w9 v) = ρ w12 v := by
  apply difference_step h (rootElement 1 0) w9 w12
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action52 : difference ρ (rootElement 2 0) (ρ w12 v) = ρ w16 v := by
  apply difference_step h (rootElement 2 0) w12 w16
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action53 : difference ρ (rootElement 3 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w1
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action54 : difference ρ (rootElement 0 1) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w6
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action55 : difference ρ (rootElement 0 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w7
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action56 : difference ρ (rootElement 0 1) (ρ w8 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 1) w8 w3
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action57 : difference ρ (rootElement 3 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 3 1) w3
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action58 : difference ρ (rootElement 0 1) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w9
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action59 : difference ρ (rootElement 0 1) (ρ w10 v) = ρ w6 v := by
  apply difference_step h (rootElement 0 1) w10 w6
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action60 : difference ρ (rootElement 3 1) (ρ w6 v) = ρ w11 v := by
  apply difference_step h (rootElement 3 1) w6 w11
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action61 : difference ρ (rootElement 1 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w4
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action62 : difference ρ (rootElement 1 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w5
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action63 : difference ρ (rootElement 1 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w6
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action64 : difference ρ (rootElement 1 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w7
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action65 : difference ρ (rootElement 1 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w8
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action66 : difference ρ (rootElement 1 3) (ρ w9 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 3) w9 w4
    [] [] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action67 : difference ρ (rootElement 1 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w10
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action68 : difference ρ (rootElement 1 3) (ρ w11 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 3) w11 w6
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action69 : difference ρ (rootElement 2 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w1
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action70 : difference ρ (rootElement 2 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w3
    [2] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action71 : difference ρ (rootElement 2 1) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w6
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action72 : difference ρ (rootElement 0 1) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w11
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action73 : difference ρ (rootElement 0 1) (ρ w12 v) = ρ w9 v := by
  apply difference_step h (rootElement 0 1) w12 w9
    [0] [0] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action74 : difference ρ (rootElement 2 1) (ρ w9 v) = ρ w17 v := by
  apply difference_step h (rootElement 2 1) w9 w17
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action75 : difference ρ (rootElement 0 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w0
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action76 : difference ρ (rootElement 0 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w1
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action77 : difference ρ (rootElement 0 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action78 : difference ρ (rootElement 0 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w3
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action79 : difference ρ (rootElement 0 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w4
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action80 : difference ρ (rootElement 0 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action81 : difference ρ (rootElement 0 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w6
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action82 : difference ρ (rootElement 0 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w7
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action83 : difference ρ (rootElement 0 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w8
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action84 : difference ρ (rootElement 0 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w9
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action85 : difference ρ (rootElement 0 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w10
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action86 : difference ρ (rootElement 0 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w11
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action87 : difference ρ (rootElement 0 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w12
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action88 : difference ρ (rootElement 0 4) (ρ w13 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 4) w13 w5
    [] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action89 : difference ρ (rootElement 2 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w2
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action90 : difference ρ (rootElement 1 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w8
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action91 : difference ρ (rootElement 1 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w9
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action92 : difference ρ (rootElement 1 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w10
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action93 : difference ρ (rootElement 1 4) (ρ w11 v) = ρ w1 v := by
  apply difference_step h (rootElement 1 4) w11 w1
    [] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action94 : difference ρ (rootElement 2 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w1
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action95 : difference ρ (rootElement 1 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action96 : difference ρ (rootElement 1 4) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w13
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action97 : difference ρ (rootElement 1 4) (ρ w14 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 4) w14 w4
    [] [2] (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) <;> decide +kernel

private theorem action98 : difference ρ (rootElement 2 3) (ρ w4 v) = ρ w2 v := by
  apply difference_step h (rootElement 2 3) w4 w2
    [2] [2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 15 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v, ρ w11 v, ρ w12 v, ρ w13 v, ρ w14 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 15 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 1 0)).comp (LinearMap.id),
    (difference ρ (rootElement 3 4)).comp (LinearMap.id),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 2 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 3 0)).comp ((difference ρ (rootElement 1 0)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 2 0)).comp ((difference ρ (rootElement 1 0)).comp (LinearMap.id)),
    (difference ρ (rootElement 3 1)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 0)).comp ((difference ρ (rootElement 1 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 4)).comp (LinearMap.id),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id))]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference ρ (rootElement 1 0) (ρ w0 v) = 0
      rw [action0 h]
    · change difference ρ (rootElement 3 4) (ρ w0 v) = 0
      rw [action2 h]
    · change difference ρ (rootElement 3 4) (ρ w1 v) = 0
      rw [action3 h]
    · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
      rw [action5 h]
    · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
      rw [action6 h]
    · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
      rw [action7 h]
    · change difference ρ (rootElement 2 4) (ρ w0 v) = 0
      rw [action9 h]
    · change difference ρ (rootElement 2 4) (ρ w1 v) = 0
      rw [action10 h]
    · change difference ρ (rootElement 2 4) (ρ w2 v) = 0
      rw [action11 h]
    · change difference ρ (rootElement 2 4) (ρ w3 v) = 0
      rw [action12 h]
    · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
      rw [action14 h]
    · change difference ρ (rootElement 0 1) (ρ w1 v) = 0
      rw [action15 h]
    · change difference ρ (rootElement 0 1) (ρ w2 v) = 0
      rw [action16 h]
    · change difference ρ (rootElement 0 1) (ρ w3 v) = 0
      rw [action17 h]
    · change difference ρ (rootElement 0 1) (ρ w4 v) = 0
      rw [action18 h]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w0 v)) = 0
      rw [action0 h, map_zero]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w1 v)) = 0
      rw [action1 h, action20 h]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w2 v)) = 0
      rw [action21 h, map_zero]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w3 v)) = 0
      rw [action22 h, action23 h]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w4 v)) = 0
      rw [action24 h, map_zero]
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w5 v)) = 0
      rw [action25 h, map_zero]
    · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
      rw [action28 h]
    · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
      rw [action29 h]
    · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
      rw [action30 h]
    · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
      rw [action31 h]
    · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
      rw [action32 h]
    · change difference ρ (rootElement 1 4) (ρ w5 v) = 0
      rw [action33 h]
    · change difference ρ (rootElement 1 4) (ρ w6 v) = 0
      rw [action34 h]
    · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
      rw [action36 h]
    · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
      rw [action37 h]
    · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
      rw [action38 h]
    · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
      rw [action39 h]
    · change difference ρ (rootElement 0 3) (ρ w4 v) = 0
      rw [action40 h]
    · change difference ρ (rootElement 0 3) (ρ w5 v) = 0
      rw [action41 h]
    · change difference ρ (rootElement 0 3) (ρ w6 v) = 0
      rw [action42 h]
    · change difference ρ (rootElement 0 3) (ρ w7 v) = 0
      rw [action43 h]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w0 v)) = 0
      rw [action0 h, map_zero]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w1 v)) = 0
      rw [action1 h, action45 h]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w2 v)) = 0
      rw [action21 h, map_zero]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w3 v)) = 0
      rw [action22 h, action46 h]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w4 v)) = 0
      rw [action24 h, map_zero]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w5 v)) = 0
      rw [action25 h, map_zero]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w6 v)) = 0
      rw [action26 h, action47 h]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w7 v)) = 0
      rw [action48 h, action49 h]
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w8 v)) = 0
      rw [action50 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
      rw [action14 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
      rw [action15 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
      rw [action16 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
      rw [action17 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
      rw [action18 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
      rw [action19 h, action53 h]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
      rw [action54 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
      rw [action55 h, map_zero]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w8 v)) = 0
      rw [action56 h, action57 h]
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w9 v)) = 0
      rw [action58 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w0 v)) = 0
      rw [action5 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w1 v)) = 0
      rw [action6 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w2 v)) = 0
      rw [action7 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w3 v)) = 0
      rw [action8 h, action0 h]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w4 v)) = 0
      rw [action61 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w5 v)) = 0
      rw [action62 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w6 v)) = 0
      rw [action63 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w7 v)) = 0
      rw [action64 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w8 v)) = 0
      rw [action65 h, map_zero]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w9 v)) = 0
      rw [action66 h, action24 h]
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w10 v)) = 0
      rw [action67 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
      rw [action14 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
      rw [action15 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
      rw [action16 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
      rw [action17 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
      rw [action18 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
      rw [action19 h, action69 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
      rw [action54 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
      rw [action55 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w8 v)) = 0
      rw [action56 h, action70 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w9 v)) = 0
      rw [action58 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w10 v)) = 0
      rw [action59 h, action71 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w11 v)) = 0
      rw [action72 h, map_zero]
    · change difference ρ (rootElement 0 4) (ρ w0 v) = 0
      rw [action75 h]
    · change difference ρ (rootElement 0 4) (ρ w1 v) = 0
      rw [action76 h]
    · change difference ρ (rootElement 0 4) (ρ w2 v) = 0
      rw [action77 h]
    · change difference ρ (rootElement 0 4) (ρ w3 v) = 0
      rw [action78 h]
    · change difference ρ (rootElement 0 4) (ρ w4 v) = 0
      rw [action79 h]
    · change difference ρ (rootElement 0 4) (ρ w5 v) = 0
      rw [action80 h]
    · change difference ρ (rootElement 0 4) (ρ w6 v) = 0
      rw [action81 h]
    · change difference ρ (rootElement 0 4) (ρ w7 v) = 0
      rw [action82 h]
    · change difference ρ (rootElement 0 4) (ρ w8 v) = 0
      rw [action83 h]
    · change difference ρ (rootElement 0 4) (ρ w9 v) = 0
      rw [action84 h]
    · change difference ρ (rootElement 0 4) (ρ w10 v) = 0
      rw [action85 h]
    · change difference ρ (rootElement 0 4) (ρ w11 v) = 0
      rw [action86 h]
    · change difference ρ (rootElement 0 4) (ρ w12 v) = 0
      rw [action87 h]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
      rw [action29 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
      rw [action30 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
      rw [action31 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
      rw [action32 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
      rw [action33 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
      rw [action34 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
      rw [action35 h, action89 h]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
      rw [action90 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
      rw [action91 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w10 v)) = 0
      rw [action92 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w11 v)) = 0
      rw [action93 h, action94 h]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w12 v)) = 0
      rw [action95 h, map_zero]
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w13 v)) = 0
      rw [action96 h, map_zero]
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w5 v) ≠ 0
      rw [action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 0) (difference ρ (rootElement 1 0) (ρ w6 v)) ≠ 0
      rw [action26 h, action27 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w7 v) ≠ 0
      rw [action35 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w8 v) ≠ 0
      rw [action44 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 0) (difference ρ (rootElement 1 0) (ρ w9 v)) ≠ 0
      rw [action51 h, action52 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 1) (difference ρ (rootElement 0 1) (ρ w10 v)) ≠ 0
      rw [action59 h, action60 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (ρ w11 v)) ≠ 0
      rw [action68 h, action26 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w12 v)) ≠ 0
      rw [action73 h, action74 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (ρ w13 v) ≠ 0
      rw [action88 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w14 v)) ≠ 0
      rw [action97 h, action98 h]
      exact translate_ne_zero ρ _ hv

theorem degree_le [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    15 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case13
