module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Twenty-five independent translates for support `{0, 2}`

Starting with a nonzero local highest vector, this certificate selects twenty-five
permutation translates. Composites of at most three root-difference operators
kill the preceding vectors and send the selected vector to a nonzero translate.
The identities use only upper-root fixedness, inactive exchanges and the active
rank-one relation, via `Separated.Extraction`; no irreducibility or comparison
with algebraic highest weights is needed. Matrix identities are checked by the
kernel. The separate row lemmas keep elaboration of the triangular array bounded.

Source application: Guralnick–Malle, *Classification of 2F-modules II*,
Lemma 4.2/Table 6 and Proposition 4.8(3B), author manuscript pp.22–23, 27–28;
Aschbacher–Smith K.3.2, printed pp.454–455. This is a direct sufficient dimension
estimate on the original binary module. It extends the eleven-vector method in
`Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case02`.
-/

@[expose] public section

open Representation.SL5TenDimensional
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.SeparatedDimension.Case02
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {0, 2} v)
include h

private def permutationElement (p : Equiv.Perm (Fin 5)) : Group :=
  ⟨p.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs] <;>
      decide +kernel⟩

private def w0 : Group := permutationElement
  { toFun := ![0, 1, 2, 3, 4]
    invFun := ![0, 1, 2, 3, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w1 : Group := permutationElement
  { toFun := ![1, 0, 2, 3, 4]
    invFun := ![1, 0, 2, 3, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w2 : Group := permutationElement
  { toFun := ![0, 1, 3, 2, 4]
    invFun := ![0, 1, 3, 2, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w3 : Group := permutationElement
  { toFun := ![1, 2, 0, 3, 4]
    invFun := ![2, 0, 1, 3, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w4 : Group := permutationElement
  { toFun := ![0, 3, 1, 2, 4]
    invFun := ![0, 2, 3, 1, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w5 : Group := permutationElement
  { toFun := ![1, 0, 3, 2, 4]
    invFun := ![1, 0, 3, 2, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w6 : Group := permutationElement
  { toFun := ![0, 1, 3, 4, 2]
    invFun := ![0, 1, 4, 2, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w7 : Group := permutationElement
  { toFun := ![3, 0, 1, 2, 4]
    invFun := ![1, 2, 3, 0, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w8 : Group := permutationElement
  { toFun := ![1, 3, 0, 2, 4]
    invFun := ![2, 0, 3, 1, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w9 : Group := permutationElement
  { toFun := ![1, 2, 3, 0, 4]
    invFun := ![3, 0, 1, 2, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w10 : Group := permutationElement
  { toFun := ![0, 3, 1, 4, 2]
    invFun := ![0, 2, 4, 1, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w11 : Group := permutationElement
  { toFun := ![1, 0, 3, 4, 2]
    invFun := ![1, 0, 4, 2, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w12 : Group := permutationElement
  { toFun := ![3, 1, 0, 2, 4]
    invFun := ![2, 1, 3, 0, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w13 : Group := permutationElement
  { toFun := ![1, 3, 2, 0, 4]
    invFun := ![3, 0, 2, 1, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w14 : Group := permutationElement
  { toFun := ![0, 3, 4, 1, 2]
    invFun := ![0, 3, 4, 1, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w15 : Group := permutationElement
  { toFun := ![3, 0, 1, 4, 2]
    invFun := ![1, 2, 4, 0, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w16 : Group := permutationElement
  { toFun := ![1, 3, 0, 4, 2]
    invFun := ![2, 0, 4, 1, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w17 : Group := permutationElement
  { toFun := ![1, 2, 3, 4, 0]
    invFun := ![4, 0, 1, 2, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w18 : Group := permutationElement
  { toFun := ![3, 1, 2, 0, 4]
    invFun := ![3, 1, 2, 0, 4]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w19 : Group := permutationElement
  { toFun := ![3, 0, 4, 1, 2]
    invFun := ![1, 3, 4, 0, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w20 : Group := permutationElement
  { toFun := ![1, 3, 4, 0, 2]
    invFun := ![3, 0, 4, 1, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w21 : Group := permutationElement
  { toFun := ![3, 1, 0, 4, 2]
    invFun := ![2, 1, 4, 0, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w22 : Group := permutationElement
  { toFun := ![1, 3, 2, 4, 0]
    invFun := ![4, 0, 2, 1, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w23 : Group := permutationElement
  { toFun := ![3, 4, 0, 1, 2]
    invFun := ![2, 3, 4, 0, 1]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w24 : Group := permutationElement
  { toFun := ![3, 1, 4, 0, 2]
    invFun := ![3, 1, 4, 0, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w25 : Group := permutationElement
  { toFun := ![1, 3, 4, 2, 0]
    invFun := ![4, 0, 3, 1, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w26 : Group := permutationElement
  { toFun := ![3, 1, 2, 4, 0]
    invFun := ![4, 1, 2, 0, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w27 : Group := permutationElement
  { toFun := ![3, 4, 1, 0, 2]
    invFun := ![3, 2, 4, 0, 1]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w28 : Group := permutationElement
  { toFun := ![3, 1, 4, 2, 0]
    invFun := ![4, 1, 3, 0, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
private def w29 : Group := permutationElement
  { toFun := ![3, 4, 1, 2, 0]
    invFun := ![4, 2, 3, 0, 1]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

private theorem action0 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action1 : difference ρ (rootElement 0 1) (ρ w1 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 1) w1 w0
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action2 : difference ρ (rootElement 2 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w0
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action3 : difference ρ (rootElement 2 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w1
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action4 : difference ρ (rootElement 2 3) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 3) w2 w0
    [] [] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action5 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action6 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action7 : difference ρ (rootElement 0 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w2
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action8 : difference ρ (rootElement 0 2) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 2) w3 w0
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action9 : difference ρ (rootElement 1 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w0
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action10 : difference ρ (rootElement 1 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w1
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action11 : difference ρ (rootElement 1 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action12 : difference ρ (rootElement 1 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w3
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action13 : difference ρ (rootElement 1 3) (ρ w4 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 3) w4 w0
    [] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action14 : difference ρ (rootElement 2 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w0
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action15 : difference ρ (rootElement 0 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action16 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action17 : difference ρ (rootElement 0 1) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w4
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action18 : difference ρ (rootElement 0 1) (ρ w5 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 1) w5 w2
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action19 : difference ρ (rootElement 2 1) (ρ w2 v) = ρ w4 v := by
  apply difference_step h (rootElement 2 1) w2 w4
    [1] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action20 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action21 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action22 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action23 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action24 : difference ρ (rootElement 2 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w4
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action25 : difference ρ (rootElement 2 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w5
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action26 : difference ρ (rootElement 2 4) (ρ w6 v) = ρ w0 v := by
  apply difference_step h (rootElement 2 4) w6 w0
    [] [3] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action27 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action28 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action29 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action30 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action31 : difference ρ (rootElement 0 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w4
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action32 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action33 : difference ρ (rootElement 0 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w6
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action34 : difference ρ (rootElement 0 3) (ρ w7 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 3) w7 w1
    [] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action35 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action36 : difference ρ (rootElement 0 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w4
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action37 : difference ρ (rootElement 0 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action38 : difference ρ (rootElement 0 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w6
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action39 : difference ρ (rootElement 0 2) (ρ w7 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 2) w7 w5
    [1] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action40 : difference ρ (rootElement 1 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w5
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action41 : difference ρ (rootElement 0 2) (ρ w8 v) = ρ w4 v := by
  apply difference_step h (rootElement 0 2) w8 w4
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action42 : difference ρ (rootElement 1 2) (ρ w4 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 2) w4 w2
    [1] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action43 : difference ρ (rootElement 1 0) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w1
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action44 : difference ρ (rootElement 0 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w8
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action45 : difference ρ (rootElement 0 3) (ρ w9 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 3) w9 w2
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action46 : difference ρ (rootElement 1 0) (ρ w2 v) = ρ w5 v := by
  apply difference_step h (rootElement 1 0) w2 w5
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action47 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action48 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action49 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action50 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action51 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action52 : difference ρ (rootElement 1 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action53 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action54 : difference ρ (rootElement 1 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w7
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action55 : difference ρ (rootElement 1 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w8
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action56 : difference ρ (rootElement 1 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w9
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action57 : difference ρ (rootElement 1 4) (ρ w10 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 4) w10 w0
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action58 : difference ρ (rootElement 2 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w7
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action59 : difference ρ (rootElement 2 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w8
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action60 : difference ρ (rootElement 2 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w9
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action61 : difference ρ (rootElement 2 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w10
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action62 : difference ρ (rootElement 2 4) (ρ w11 v) = ρ w1 v := by
  apply difference_step h (rootElement 2 4) w11 w1
    [] [3] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action63 : difference ρ (rootElement 0 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w10
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action64 : difference ρ (rootElement 0 3) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w11
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action65 : difference ρ (rootElement 0 3) (ρ w12 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 3) w12 w3
    [] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action66 : difference ρ (rootElement 0 3) (ρ w13 v) = ρ w4 v := by
  apply difference_step h (rootElement 0 3) w13 w4
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action67 : difference ρ (rootElement 1 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w11
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action68 : difference ρ (rootElement 1 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action69 : difference ρ (rootElement 1 4) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w13
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action70 : difference ρ (rootElement 1 4) (ρ w14 v) = ρ w2 v := by
  apply difference_step h (rootElement 1 4) w14 w2
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action71 : difference ρ (rootElement 0 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w0
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action72 : difference ρ (rootElement 0 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w1
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action73 : difference ρ (rootElement 0 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action74 : difference ρ (rootElement 0 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w3
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action75 : difference ρ (rootElement 0 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w4
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action76 : difference ρ (rootElement 0 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action77 : difference ρ (rootElement 0 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w6
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action78 : difference ρ (rootElement 0 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w7
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action79 : difference ρ (rootElement 0 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w8
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action80 : difference ρ (rootElement 0 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w9
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action81 : difference ρ (rootElement 0 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w10
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action82 : difference ρ (rootElement 0 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w11
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action83 : difference ρ (rootElement 0 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w12
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action84 : difference ρ (rootElement 0 4) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w13
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action85 : difference ρ (rootElement 0 4) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w14
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action86 : difference ρ (rootElement 0 4) (ρ w15 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 4) w15 w1
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action87 : difference ρ (rootElement 1 4) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w15
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action88 : difference ρ (rootElement 1 4) (ρ w16 v) = ρ w3 v := by
  apply difference_step h (rootElement 1 4) w16 w3
    [] [3] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action89 : difference ρ (rootElement 0 4) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w16
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action90 : difference ρ (rootElement 0 4) (ρ w17 v) = ρ w6 v := by
  apply difference_step h (rootElement 0 4) w17 w6
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action91 : difference ρ (rootElement 1 0) (ρ w6 v) = ρ w11 v := by
  apply difference_step h (rootElement 1 0) w6 w11
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action92 : difference ρ (rootElement 0 3) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w14
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action93 : difference ρ (rootElement 0 3) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w15
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action94 : difference ρ (rootElement 0 3) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w16
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action95 : difference ρ (rootElement 0 3) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w17
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action96 : difference ρ (rootElement 0 3) (ρ w19 v) = ρ w11 v := by
  apply difference_step h (rootElement 0 3) w19 w11
    [1] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action97 : difference ρ (rootElement 0 3) (ρ w20 v) = ρ w14 v := by
  apply difference_step h (rootElement 0 3) w20 w14
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action98 : difference ρ (rootElement 0 4) (ρ w19 v) = ρ w5 v := by
  apply difference_step h (rootElement 0 4) w19 w5
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action99 : difference ρ (rootElement 0 4) (ρ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w20
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action100 : difference ρ (rootElement 0 4) (ρ w21 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 4) w21 w3
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action101 : difference ρ (rootElement 0 4) (ρ w22 v) = ρ w10 v := by
  apply difference_step h (rootElement 0 4) w22 w10
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action102 : difference ρ (rootElement 1 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w6
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action103 : difference ρ (rootElement 1 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w5
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action104 : difference ρ (rootElement 1 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w10
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action105 : difference ρ (rootElement 0 4) (ρ w23 v) = ρ w8 v := by
  apply difference_step h (rootElement 0 4) w23 w8
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action106 : difference ρ (rootElement 1 3) (ρ w8 v) = ρ w3 v := by
  apply difference_step h (rootElement 1 3) w8 w3
    [] [] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action107 : difference ρ (rootElement 0 4) (ρ w24 v) = ρ w9 v := by
  apply difference_step h (rootElement 0 4) w24 w9
    [] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private theorem action108 : difference ρ (rootElement 1 0) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w3
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action109 : difference ρ (rootElement 1 3) (ρ w9 v) = ρ w5 v := by
  apply difference_step h (rootElement 1 3) w9 w5
    [1] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action110 : difference ρ (rootElement 1 0) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w5
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action111 : difference ρ (rootElement 0 4) (ρ w25 v) = ρ w14 v := by
  apply difference_step h (rootElement 0 4) w25 w14
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)
    <;> decide +kernel

private theorem action112 : difference ρ (rootElement 1 3) (ρ w14 v) = ρ w6 v := by
  apply difference_step h (rootElement 1 3) w14 w6
    [1] [3, 1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)
    <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 25 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v, ρ w11 v, ρ w12 v, ρ w13 v, ρ w14 v, ρ w15 v, ρ w16 v, ρ w17 v, ρ w19 v, ρ w20 v, ρ w21 v, ρ w22 v, ρ w23 v, ρ w24 v, ρ w25 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 25 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 2 3)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp (LinearMap.id),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 0)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 0)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 4)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 3)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 0)).comp ((difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)))]

private theorem row1 (j : Fin 25) (hj : j < 1) :
    extractors ρ 1 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
    rw [action0 h]

private theorem row2 (j : Fin 25) (hj : j < 2) :
    extractors ρ 2 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 2 3) (ρ w0 v) = 0
    rw [action2 h]
  · change difference ρ (rootElement 2 3) (ρ w1 v) = 0
    rw [action3 h]

private theorem row3 (j : Fin 25) (hj : j < 3) :
    extractors ρ 3 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 2) (ρ w0 v) = 0
    rw [action5 h]
  · change difference ρ (rootElement 0 2) (ρ w1 v) = 0
    rw [action6 h]
  · change difference ρ (rootElement 0 2) (ρ w2 v) = 0
    rw [action7 h]

private theorem row4 (j : Fin 25) (hj : j < 4) :
    extractors ρ 4 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
    rw [action9 h]
  · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
    rw [action10 h]
  · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
    rw [action11 h]
  · change difference ρ (rootElement 1 3) (ρ w3 v) = 0
    rw [action12 h]

private theorem row5 (j : Fin 25) (hj : j < 5) :
    extractors ρ 5 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
    rw [action0 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
    rw [action1 h, action14 h]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
    rw [action15 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
    rw [action16 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
    rw [action17 h, map_zero]

private theorem row6 (j : Fin 25) (hj : j < 6) :
    extractors ρ 6 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 2 4) (ρ w0 v) = 0
    rw [action20 h]
  · change difference ρ (rootElement 2 4) (ρ w1 v) = 0
    rw [action21 h]
  · change difference ρ (rootElement 2 4) (ρ w2 v) = 0
    rw [action22 h]
  · change difference ρ (rootElement 2 4) (ρ w3 v) = 0
    rw [action23 h]
  · change difference ρ (rootElement 2 4) (ρ w4 v) = 0
    rw [action24 h]
  · change difference ρ (rootElement 2 4) (ρ w5 v) = 0
    rw [action25 h]

private theorem row7 (j : Fin 25) (hj : j < 7) :
    extractors ρ 7 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
    rw [action27 h]
  · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
    rw [action28 h]
  · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
    rw [action29 h]
  · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
    rw [action30 h]
  · change difference ρ (rootElement 0 3) (ρ w4 v) = 0
    rw [action31 h]
  · change difference ρ (rootElement 0 3) (ρ w5 v) = 0
    rw [action32 h]
  · change difference ρ (rootElement 0 3) (ρ w6 v) = 0
    rw [action33 h]

private theorem row8 (j : Fin 25) (hj : j < 8) :
    extractors ρ 8 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
    rw [action5 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
    rw [action6 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
    rw [action7 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
    rw [action8 h, action35 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
    rw [action36 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
    rw [action37 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
    rw [action38 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w7 v)) = 0
    rw [action39 h, action40 h]

private theorem row9 (j : Fin 25) (hj : j < 9) :
    extractors ρ 9 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    rw [action27 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    rw [action28 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    rw [action29 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    rw [action30 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    rw [action31 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    rw [action32 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    rw [action33 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    rw [action34 h, action43 h]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    rw [action44 h, map_zero]

private theorem row10 (j : Fin 25) (hj : j < 10) :
    extractors ρ 10 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
    rw [action47 h]
  · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
    rw [action48 h]
  · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
    rw [action49 h]
  · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
    rw [action50 h]
  · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
    rw [action51 h]
  · change difference ρ (rootElement 1 4) (ρ w5 v) = 0
    rw [action52 h]
  · change difference ρ (rootElement 1 4) (ρ w6 v) = 0
    rw [action53 h]
  · change difference ρ (rootElement 1 4) (ρ w7 v) = 0
    rw [action54 h]
  · change difference ρ (rootElement 1 4) (ρ w8 v) = 0
    rw [action55 h]
  · change difference ρ (rootElement 1 4) (ρ w9 v) = 0
    rw [action56 h]

private theorem row11 (j : Fin 25) (hj : j < 11) :
    extractors ρ 11 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w0 v)) = 0
    rw [action20 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w1 v)) = 0
    rw [action21 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w2 v)) = 0
    rw [action22 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w3 v)) = 0
    rw [action23 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w4 v)) = 0
    rw [action24 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w5 v)) = 0
    rw [action25 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w6 v)) = 0
    rw [action26 h, action0 h]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w7 v)) = 0
    rw [action58 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w8 v)) = 0
    rw [action59 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w9 v)) = 0
    rw [action60 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w10 v)) = 0
    rw [action61 h, map_zero]

private theorem row12 (j : Fin 25) (hj : j < 12) :
    extractors ρ 12 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    rw [action27 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    rw [action28 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    rw [action29 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    rw [action30 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    rw [action31 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    rw [action32 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    rw [action33 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    rw [action34 h, action6 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    rw [action44 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    rw [action45 h, action7 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    rw [action63 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    rw [action64 h, map_zero]

private theorem row13 (j : Fin 25) (hj : j < 13) :
    extractors ρ 13 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    rw [action27 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    rw [action28 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    rw [action29 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    rw [action30 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    rw [action31 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    rw [action32 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    rw [action33 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    rw [action34 h, action10 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    rw [action44 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    rw [action45 h, action11 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    rw [action63 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    rw [action64 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w12 v)) = 0
    rw [action65 h, action12 h]

private theorem row14 (j : Fin 25) (hj : j < 14) :
    extractors ρ 14 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
    rw [action47 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
    rw [action48 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
    rw [action49 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
    rw [action50 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
    rw [action51 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
    rw [action52 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
    rw [action53 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
    rw [action54 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
    rw [action55 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
    rw [action56 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w10 v)) = 0
    rw [action57 h, action14 h]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w11 v)) = 0
    rw [action67 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w12 v)) = 0
    rw [action68 h, map_zero]
  · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w13 v)) = 0
    rw [action69 h, map_zero]

private theorem row15 (j : Fin 25) (hj : j < 15) :
    extractors ρ 15 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 4) (ρ w0 v) = 0
    rw [action71 h]
  · change difference ρ (rootElement 0 4) (ρ w1 v) = 0
    rw [action72 h]
  · change difference ρ (rootElement 0 4) (ρ w2 v) = 0
    rw [action73 h]
  · change difference ρ (rootElement 0 4) (ρ w3 v) = 0
    rw [action74 h]
  · change difference ρ (rootElement 0 4) (ρ w4 v) = 0
    rw [action75 h]
  · change difference ρ (rootElement 0 4) (ρ w5 v) = 0
    rw [action76 h]
  · change difference ρ (rootElement 0 4) (ρ w6 v) = 0
    rw [action77 h]
  · change difference ρ (rootElement 0 4) (ρ w7 v) = 0
    rw [action78 h]
  · change difference ρ (rootElement 0 4) (ρ w8 v) = 0
    rw [action79 h]
  · change difference ρ (rootElement 0 4) (ρ w9 v) = 0
    rw [action80 h]
  · change difference ρ (rootElement 0 4) (ρ w10 v) = 0
    rw [action81 h]
  · change difference ρ (rootElement 0 4) (ρ w11 v) = 0
    rw [action82 h]
  · change difference ρ (rootElement 0 4) (ρ w12 v) = 0
    rw [action83 h]
  · change difference ρ (rootElement 0 4) (ρ w13 v) = 0
    rw [action84 h]
  · change difference ρ (rootElement 0 4) (ρ w14 v) = 0
    rw [action85 h]

private theorem row16 (j : Fin 25) (hj : j < 16) :
    extractors ρ 16 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
    rw [action47 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
    rw [action48 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
    rw [action49 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
    rw [action50 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
    rw [action51 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
    rw [action52 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
    rw [action53 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
    rw [action54 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
    rw [action55 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
    rw [action56 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w10 v)) = 0
    rw [action57 h, action5 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w11 v)) = 0
    rw [action67 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w12 v)) = 0
    rw [action68 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w13 v)) = 0
    rw [action69 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w14 v)) = 0
    rw [action70 h, action7 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w15 v)) = 0
    rw [action87 h, map_zero]

private theorem row17 (j : Fin 25) (hj : j < 17) :
    extractors ρ 17 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    rw [action71 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    rw [action72 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    rw [action73 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    rw [action74 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    rw [action75 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    rw [action76 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    rw [action77 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    rw [action78 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    rw [action79 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    rw [action80 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    rw [action81 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    rw [action82 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    rw [action83 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    rw [action84 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    rw [action85 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    rw [action86 h, action43 h]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    rw [action89 h, map_zero]

private theorem row18 (j : Fin 25) (hj : j < 18) :
    extractors ρ 18 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    rw [action27 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    rw [action28 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    rw [action29 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    rw [action30 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    rw [action31 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    rw [action32 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    rw [action33 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    rw [action34 h, action21 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    rw [action44 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    rw [action45 h, action22 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    rw [action63 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    rw [action64 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w12 v)) = 0
    rw [action65 h, action23 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w13 v)) = 0
    rw [action66 h, action24 h]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w14 v)) = 0
    rw [action92 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w15 v)) = 0
    rw [action93 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w16 v)) = 0
    rw [action94 h, map_zero]
  · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w17 v)) = 0
    rw [action95 h, map_zero]

private theorem row19 (j : Fin 25) (hj : j < 19) :
    extractors ρ 19 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    rw [action27 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    rw [action28 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    rw [action29 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    rw [action30 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    rw [action31 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    rw [action32 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    rw [action33 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    rw [action34 h, action48 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    rw [action44 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    rw [action45 h, action49 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    rw [action63 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    rw [action64 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w12 v)) = 0
    rw [action65 h, action50 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w13 v)) = 0
    rw [action66 h, action51 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w14 v)) = 0
    rw [action92 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w15 v)) = 0
    rw [action93 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w16 v)) = 0
    rw [action94 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w17 v)) = 0
    rw [action95 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w19 v)) = 0
    rw [action96 h, action67 h]

private theorem row20 (j : Fin 25) (hj : j < 20) :
    extractors ρ 20 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    rw [action71 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    rw [action72 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    rw [action73 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    rw [action74 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    rw [action75 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    rw [action76 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    rw [action77 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    rw [action78 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    rw [action79 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    rw [action80 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    rw [action81 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    rw [action82 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    rw [action83 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    rw [action84 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    rw [action85 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    rw [action86 h, action6 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    rw [action89 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    rw [action90 h, action38 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    rw [action98 h, action37 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    rw [action99 h, map_zero]

private theorem row21 (j : Fin 25) (hj : j < 21) :
    extractors ρ 21 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    rw [action71 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    rw [action72 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    rw [action73 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    rw [action74 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    rw [action75 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    rw [action76 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    rw [action77 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    rw [action78 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    rw [action79 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    rw [action80 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    rw [action81 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    rw [action82 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    rw [action83 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    rw [action84 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    rw [action85 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    rw [action86 h, action48 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    rw [action89 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    rw [action90 h, action53 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    rw [action98 h, action52 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    rw [action99 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    rw [action100 h, action50 h]

private theorem row22 (j : Fin 25) (hj : j < 22) :
    extractors ρ 22 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    rw [action71 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    rw [action72 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    rw [action73 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    rw [action74 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    rw [action75 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    rw [action76 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    rw [action77 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    rw [action78 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    rw [action79 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    rw [action80 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    rw [action81 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    rw [action82 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    rw [action83 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    rw [action84 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    rw [action85 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    rw [action86 h, action10 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    rw [action89 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    rw [action90 h, action102 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    rw [action98 h, action103 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    rw [action99 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    rw [action100 h, action12 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w22 v)) = 0
    rw [action101 h, action104 h]

private theorem row23 (j : Fin 25) (hj : j < 23) :
    extractors ρ 23 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    rw [action71 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    rw [action72 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    rw [action73 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    rw [action74 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    rw [action75 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    rw [action76 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    rw [action77 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    rw [action78 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    rw [action79 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    rw [action80 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    rw [action81 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    rw [action82 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    rw [action83 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    rw [action84 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    rw [action85 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    rw [action86 h, action28 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    rw [action89 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    rw [action90 h, action33 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    rw [action98 h, action32 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    rw [action99 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    rw [action100 h, action30 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w22 v)) = 0
    rw [action101 h, action63 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w23 v)) = 0
    rw [action105 h, action44 h]

private theorem row24 (j : Fin 25) (hj : j < 24) :
    extractors ρ 24 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num [Fin.lt_def] at hj
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w0 v))) = 0
    rw [action71 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w1 v))) = 0
    rw [action72 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w2 v))) = 0
    rw [action73 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w3 v))) = 0
    rw [action74 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w4 v))) = 0
    rw [action75 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w5 v))) = 0
    rw [action76 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w6 v))) = 0
    rw [action77 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w7 v))) = 0
    rw [action78 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w8 v))) = 0
    rw [action79 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w9 v))) = 0
    rw [action80 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w10 v))) = 0
    rw [action81 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w11 v))) = 0
    rw [action82 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w12 v))) = 0
    rw [action83 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w13 v))) = 0
    rw [action84 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w14 v))) = 0
    rw [action85 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w15 v))) = 0
    rw [action86 h, action10 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w16 v))) = 0
    rw [action89 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w17 v))) = 0
    rw [action90 h, action102 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w19 v))) = 0
    rw [action98 h, action103 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w20 v))) = 0
    rw [action99 h, map_zero, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w21 v))) = 0
    rw [action100 h, action12 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w22 v))) = 0
    rw [action101 h, action104 h, map_zero]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w23 v))) = 0
    rw [action105 h, action106 h, action108 h]
  · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w24 v))) = 0
    rw [action107 h, action109 h, action110 h]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i
    · exact (Fin.not_lt_zero j hij).elim
    · exact row1 h j hij
    · exact row2 h j hij
    · exact row3 h j hij
    · exact row4 h j hij
    · exact row5 h j hij
    · exact row6 h j hij
    · exact row7 h j hij
    · exact row8 h j hij
    · exact row9 h j hij
    · exact row10 h j hij
    · exact row11 h j hij
    · exact row12 h j hij
    · exact row13 h j hij
    · exact row14 h j hij
    · exact row15 h j hij
    · exact row16 h j hij
    · exact row17 h j hij
    · exact row18 h j hij
    · exact row19 h j hij
    · exact row20 h j hij
    · exact row21 h j hij
    · exact row22 h j hij
    · exact row23 h j hij
    · exact row24 h j hij
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w5 v)) ≠ 0
      rw [action18 h, action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (ρ w6 v) ≠ 0
      rw [action26 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w7 v) ≠ 0
      rw [action34 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w8 v)) ≠ 0
      rw [action41 h, action42 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 3) (ρ w9 v)) ≠ 0
      rw [action45 h, action46 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w10 v) ≠ 0
      rw [action57 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w11 v)) ≠ 0
      rw [action62 h, action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 3) (ρ w12 v)) ≠ 0
      rw [action65 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w13 v)) ≠ 0
      rw [action66 h, action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 1 4) (ρ w14 v)) ≠ 0
      rw [action70 h, action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (ρ w15 v) ≠ 0
      rw [action86 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w16 v)) ≠ 0
      rw [action88 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 0 4) (ρ w17 v)) ≠ 0
      rw [action90 h, action91 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (difference ρ (rootElement 0 3) (ρ w19 v)) ≠ 0
      rw [action96 h, action62 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 3) (ρ w20 v)) ≠ 0
      rw [action97 h, action70 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 0 4) (ρ w21 v)) ≠ 0
      rw [action100 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w22 v)) ≠ 0
      rw [action101 h, action57 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w23 v)) ≠ 0
      rw [action105 h, action106 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (difference ρ (rootElement 0 4) (ρ w24 v)) ≠ 0
      rw [action107 h, action45 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (difference ρ (rootElement 1 3) (difference ρ (rootElement 0 4) (ρ w25 v))) ≠ 0
      rw [action111 h, action112 h, action91 h]
      exact translate_ne_zero ρ _ hv

/-- Twenty-five permutation translates of any nonzero local highest vector are independent. -/
theorem twentyFive_le [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    25 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.SeparatedDimension.Case02
