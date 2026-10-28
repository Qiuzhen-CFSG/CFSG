module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction

/-!
# Twenty-five independent translates with three active roots

The certificate uses only upper fixedness and the three indicated active
rank-one relations; any additional roots may also be active. Each root
difference either kills a permutation translate or gives another permutation
translate. The listed products of differences kill every preceding vector
and take their own vector to a nonzero translate, proving independence.
The finite matrix identities are checked by kernel reduction.

This supplies the additional-support branch of the local dimension estimate
used for Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8(3B),
and Aschbacher–Smith K.3.2, printed pp.454–455. It uses no comparison with
algebraic highest weights.
-/

@[expose] public section
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.Three013
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V}
variable {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v)
variable (h0 : (0 : Fin 4) ∈ J) (h1 : (1 : Fin 4) ∈ J) (h3 : (3 : Fin 4) ∈ J)
include h

private def permutationSL (p : Equiv.Perm (Fin 5)) :
    Representation.SL5TenDimensional.Group :=
  ⟨(1 : Matrix (Fin 5) (Fin 5) (ZMod 2)).submatrix id p, by
    rw [Matrix.det_permute', Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp]
    all_goals decide⟩

private def w0 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide +kernel, by decide +kernel⟩
private def w1 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 0, 2, 3, 4], ![1, 0, 2, 3, 4], by decide +kernel, by decide +kernel⟩
private def w2 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 1, 3, 4], ![0, 2, 1, 3, 4], by decide +kernel, by decide +kernel⟩
private def w3 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide +kernel, by decide +kernel⟩
private def w4 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide +kernel, by decide +kernel⟩
private def w5 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide +kernel, by decide +kernel⟩
private def w6 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 1, 2, 4], ![0, 2, 3, 1, 4], by decide +kernel, by decide +kernel⟩
private def w7 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], by decide +kernel, by decide +kernel⟩
private def w8 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], by decide +kernel, by decide +kernel⟩
private def w9 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 1, 4, 3], ![0, 2, 1, 4, 3], by decide +kernel, by decide +kernel⟩
private def w10 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 3, 4, 1], ![0, 4, 1, 2, 3], by decide +kernel, by decide +kernel⟩
private def w11 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 0, 2, 4], ![2, 0, 3, 1, 4], by decide +kernel, by decide +kernel⟩
private def w12 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![3, 0, 1, 2, 4], ![1, 2, 3, 0, 4], by decide +kernel, by decide +kernel⟩
private def w13 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 0, 3, 4, 2], ![1, 0, 4, 2, 3], by decide +kernel, by decide +kernel⟩
private def w14 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 1, 4, 2], ![0, 2, 4, 1, 3], by decide +kernel, by decide +kernel⟩
private def w15 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 0, 4, 3], ![2, 0, 1, 4, 3], by decide +kernel, by decide +kernel⟩
private def w16 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 0, 1, 4, 3], ![1, 2, 0, 4, 3], by decide +kernel, by decide +kernel⟩
private def w17 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide +kernel, by decide +kernel⟩
private def w18 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 0, 3, 4, 1], ![1, 4, 0, 2, 3], by decide +kernel, by decide +kernel⟩
private def w19 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 2, 4, 1], ![0, 4, 2, 1, 3], by decide +kernel, by decide +kernel⟩
private def w20 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 0, 4, 2], ![2, 0, 4, 1, 3], by decide +kernel, by decide +kernel⟩
private def w21 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![3, 0, 1, 4, 2], ![1, 2, 4, 0, 3], by decide +kernel, by decide +kernel⟩
private def w22 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![4, 0, 1, 2, 3], ![1, 2, 3, 4, 0], by decide +kernel, by decide +kernel⟩
private def w23 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 1, 3, 4, 0], ![4, 1, 0, 2, 3], by decide +kernel, by decide +kernel⟩
private def w24 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 2, 4, 0], ![4, 0, 2, 1, 3], by decide +kernel, by decide +kernel⟩
private def w25 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 3, 2, 4], ![0, 1, 3, 2, 4], by decide +kernel, by decide +kernel⟩
private def w26 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 2, 3, 1, 4], ![0, 3, 1, 2, 4], by decide +kernel, by decide +kernel⟩
private def w27 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 0, 3, 2, 4], ![1, 0, 3, 2, 4], by decide +kernel, by decide +kernel⟩
private def w28 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 2, 3, 0, 4], ![3, 0, 1, 2, 4], by decide +kernel, by decide +kernel⟩
private def w29 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 0, 3, 1, 4], ![1, 3, 0, 2, 4], by decide +kernel, by decide +kernel⟩
private def w30 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide +kernel, by decide +kernel⟩
private def w31 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 4, 1, 2, 3], ![0, 2, 3, 4, 1], by decide +kernel, by decide +kernel⟩
private def w32 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide +kernel, by decide +kernel⟩
private def w33 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![2, 1, 3, 0, 4], ![3, 1, 0, 2, 4], by decide +kernel, by decide +kernel⟩
private def w34 : Representation.SL5TenDimensional.Group :=
  permutationSL ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide +kernel, by decide +kernel⟩

attribute [local irreducible] w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34

private theorem action0 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by simp) 0 1 (by decide)
  decide +kernel

include h0 in
private theorem action1 : difference ρ (rootElement 0 1) (ρ w1 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 1) w1 w0
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action2 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action3 : difference ρ (rootElement 1 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w1
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h1 in
private theorem action4 : difference ρ (rootElement 1 2) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 1 2) w2 w0
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action5 : difference ρ (rootElement 3 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w0
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action6 : difference ρ (rootElement 3 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w1
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action7 : difference ρ (rootElement 3 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w2
    [] (by simp) 3 4 (by decide)
  decide +kernel

include h3 in
private theorem action8 : difference ρ (rootElement 3 4) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 3 4) w3 w0
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action9 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by simp) 0 2 (by decide)
  decide +kernel

private theorem action10 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action11 : difference ρ (rootElement 0 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w2
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action12 : difference ρ (rootElement 0 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w3
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h1 in
private theorem action13 : difference ρ (rootElement 0 2) (ρ w4 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 2) w4 w1
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

include h0 in
private theorem action14 : difference ρ (rootElement 0 2) (ρ w5 v) = ρ w2 v := by
  apply difference_step h (rootElement 0 2) w5 w2
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action15 : difference ρ (rootElement 1 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w0
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action16 : difference ρ (rootElement 1 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w1
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action17 : difference ρ (rootElement 1 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w2
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action18 : difference ρ (rootElement 1 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w3
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action19 : difference ρ (rootElement 1 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w4
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action20 : difference ρ (rootElement 1 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w5
    [] (by simp) 2 3 (by decide)
  decide +kernel

include h1 in
private theorem action21 : difference ρ (rootElement 1 3) (ρ w6 v) = ρ w25 v := by
  apply difference_step h (rootElement 1 3) w6 w25
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action22 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action23 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action24 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action25 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action26 : difference ρ (rootElement 2 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w4
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action27 : difference ρ (rootElement 2 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w5
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action28 : difference ρ (rootElement 2 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w6
    [] (by simp) 3 4 (by decide)
  decide +kernel

include h3 in
private theorem action29 : difference ρ (rootElement 2 4) (ρ w7 v) = ρ w25 v := by
  apply difference_step h (rootElement 2 4) w7 w25
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action30 : difference ρ (rootElement 3 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w4
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action31 : difference ρ (rootElement 3 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w5
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action32 : difference ρ (rootElement 3 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w6
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action33 : difference ρ (rootElement 3 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w7
    [] (by simp) 2 3 (by decide)
  decide +kernel

include h3 in
private theorem action34 : difference ρ (rootElement 3 4) (ρ w8 v) = ρ w1 v := by
  apply difference_step h (rootElement 3 4) w8 w1
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h3 in
private theorem action35 : difference ρ (rootElement 3 4) (ρ w9 v) = ρ w2 v := by
  apply difference_step h (rootElement 3 4) w9 w2
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action36 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action37 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action38 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action39 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action40 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action41 : difference ρ (rootElement 1 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action42 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action43 : difference ρ (rootElement 1 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w7
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action44 : difference ρ (rootElement 1 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w8
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action45 : difference ρ (rootElement 1 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w9
    [] (by simp) 2 3 (by decide)
  decide +kernel

include h3 in
private theorem action46 : difference ρ (rootElement 1 4) (ρ w10 v) = ρ w26 v := by
  apply difference_step h (rootElement 1 4) w10 w26
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action47 : difference ρ (rootElement 0 3) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w0
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action48 : difference ρ (rootElement 0 3) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action49 : difference ρ (rootElement 0 3) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w2
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action50 : difference ρ (rootElement 0 3) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w3
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action51 : difference ρ (rootElement 0 3) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w4
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action52 : difference ρ (rootElement 0 3) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w5
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action53 : difference ρ (rootElement 0 3) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w6
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action54 : difference ρ (rootElement 0 3) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w7
    [] (by simp) 0 2 (by decide)
  decide +kernel

private theorem action55 : difference ρ (rootElement 0 3) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w8
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action56 : difference ρ (rootElement 0 3) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w9
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action57 : difference ρ (rootElement 0 3) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w10
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h1 in
private theorem action58 : difference ρ (rootElement 0 3) (ρ w11 v) = ρ w27 v := by
  apply difference_step h (rootElement 0 3) w11 w27
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action59 : difference ρ (rootElement 1 3) (ρ w27 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w27
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h0 in
private theorem action60 : difference ρ (rootElement 0 3) (ρ w12 v) = ρ w6 v := by
  apply difference_step h (rootElement 0 3) w12 w6
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action61 : difference ρ (rootElement 0 1) (ρ w25 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w25
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action62 : difference ρ (rootElement 2 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w8
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action63 : difference ρ (rootElement 2 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w9
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action64 : difference ρ (rootElement 2 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w10
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action65 : difference ρ (rootElement 2 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w11
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action66 : difference ρ (rootElement 2 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w12
    [] (by simp) 3 4 (by decide)
  decide +kernel

include h3 in
private theorem action67 : difference ρ (rootElement 2 4) (ρ w13 v) = ρ w27 v := by
  apply difference_step h (rootElement 2 4) w13 w27
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h0 in
private theorem action68 : difference ρ (rootElement 0 1) (ρ w27 v) = ρ w25 v := by
  apply difference_step h (rootElement 0 1) w27 w25
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action69 : difference ρ (rootElement 1 3) (ρ w25 v) = 0 := by
  apply difference_zero h (rootElement 1 3) w25
    [] (by simp) 1 2 (by decide)
  decide +kernel

include h3 in
private theorem action70 : difference ρ (rootElement 2 4) (ρ w14 v) = ρ w6 v := by
  apply difference_step h (rootElement 2 4) w14 w6
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action71 : difference ρ (rootElement 0 2) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w6
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action72 : difference ρ (rootElement 0 2) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w7
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action73 : difference ρ (rootElement 0 2) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w8
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action74 : difference ρ (rootElement 0 2) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w9
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action75 : difference ρ (rootElement 0 2) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w10
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action76 : difference ρ (rootElement 0 2) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w11
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action77 : difference ρ (rootElement 0 2) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w12
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action78 : difference ρ (rootElement 0 2) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w13
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action79 : difference ρ (rootElement 0 2) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w14
    [] (by simp) 0 4 (by decide)
  decide +kernel

include h1 in
private theorem action80 : difference ρ (rootElement 0 2) (ρ w15 v) = ρ w8 v := by
  apply difference_step h (rootElement 0 2) w15 w8
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action81 : difference ρ (rootElement 1 2) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w8
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h0 in
private theorem action82 : difference ρ (rootElement 0 2) (ρ w16 v) = ρ w9 v := by
  apply difference_step h (rootElement 0 2) w16 w9
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

include h1 in
private theorem action83 : difference ρ (rootElement 1 2) (ρ w9 v) = ρ w3 v := by
  apply difference_step h (rootElement 1 2) w9 w3
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action84 : difference ρ (rootElement 0 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w0
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action85 : difference ρ (rootElement 0 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w1
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action86 : difference ρ (rootElement 0 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w2
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action87 : difference ρ (rootElement 0 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w3
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action88 : difference ρ (rootElement 0 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w4
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action89 : difference ρ (rootElement 0 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w5
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action90 : difference ρ (rootElement 0 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w6
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action91 : difference ρ (rootElement 0 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w7
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action92 : difference ρ (rootElement 0 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w8
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action93 : difference ρ (rootElement 0 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w9
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action94 : difference ρ (rootElement 0 4) (ρ w10 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w10
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action95 : difference ρ (rootElement 0 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w11
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action96 : difference ρ (rootElement 0 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w12
    [] (by simp) 1 4 (by decide)
  decide +kernel

private theorem action97 : difference ρ (rootElement 0 4) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w13
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action98 : difference ρ (rootElement 0 4) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w14
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action99 : difference ρ (rootElement 0 4) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w15
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action100 : difference ρ (rootElement 0 4) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w16
    [] (by simp) 1 3 (by decide)
  decide +kernel

include h3 in
private theorem action101 : difference ρ (rootElement 0 4) (ρ w17 v) = ρ w28 v := by
  apply difference_step h (rootElement 0 4) w17 w28
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action102 : difference ρ (rootElement 0 2) (ρ w26 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w26
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action103 : difference ρ (rootElement 1 4) (ρ w11 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w11
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action104 : difference ρ (rootElement 1 4) (ρ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by simp) 2 4 (by decide)
  decide +kernel

private theorem action105 : difference ρ (rootElement 1 4) (ρ w13 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w13
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action106 : difference ρ (rootElement 1 4) (ρ w14 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w14
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action107 : difference ρ (rootElement 1 4) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w15
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action108 : difference ρ (rootElement 1 4) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w16
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action109 : difference ρ (rootElement 1 4) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w17
    [] (by simp) 0 3 (by decide)
  decide +kernel

include h3 in
private theorem action110 : difference ρ (rootElement 1 4) (ρ w18 v) = ρ w29 v := by
  apply difference_step h (rootElement 1 4) w18 w29
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h0 in
private theorem action111 : difference ρ (rootElement 0 2) (ρ w29 v) = ρ w26 v := by
  apply difference_step h (rootElement 0 2) w29 w26
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action112 : difference ρ (rootElement 2 3) (ρ w26 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w26
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action113 : difference ρ (rootElement 2 3) (ρ w29 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w29
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h3 in
private theorem action114 : difference ρ (rootElement 1 4) (ρ w19 v) = ρ w30 v := by
  apply difference_step h (rootElement 1 4) w19 w30
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h1 in
private theorem action115 : difference ρ (rootElement 2 3) (ρ w30 v) = ρ w26 v := by
  apply difference_step h (rootElement 2 3) w30 w26
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action116 : difference ρ (rootElement 0 3) (ρ w25 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w25
    [] (by simp) 0 2 (by decide)
  decide +kernel

private theorem action117 : difference ρ (rootElement 0 3) (ρ w27 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w27
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action118 : difference ρ (rootElement 2 4) (ρ w15 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w15
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action119 : difference ρ (rootElement 2 4) (ρ w16 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w16
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action120 : difference ρ (rootElement 2 4) (ρ w17 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w17
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action121 : difference ρ (rootElement 2 4) (ρ w18 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w18
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action122 : difference ρ (rootElement 2 4) (ρ w19 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w19
    [] (by simp) 2 3 (by decide)
  decide +kernel

include h3 in
private theorem action123 : difference ρ (rootElement 2 4) (ρ w20 v) = ρ w11 v := by
  apply difference_step h (rootElement 2 4) w20 w11
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h3 in
private theorem action124 : difference ρ (rootElement 2 4) (ρ w21 v) = ρ w12 v := by
  apply difference_step h (rootElement 2 4) w21 w12
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

private theorem action125 : difference ρ (rootElement 1 4) (ρ w28 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w28
    [] (by simp) 0 4 (by decide)
  decide +kernel

private theorem action126 : difference ρ (rootElement 0 4) (ρ w18 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w18
    [] (by simp) 1 3 (by decide)
  decide +kernel

private theorem action127 : difference ρ (rootElement 0 4) (ρ w19 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w19
    [] (by simp) 0 3 (by decide)
  decide +kernel

private theorem action128 : difference ρ (rootElement 0 4) (ρ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w20
    [] (by simp) 2 3 (by decide)
  decide +kernel

private theorem action129 : difference ρ (rootElement 0 4) (ρ w21 v) = 0 := by
  apply difference_zero h (rootElement 0 4) w21
    [] (by simp) 1 3 (by decide)
  decide +kernel

include h0 in
private theorem action130 : difference ρ (rootElement 0 4) (ρ w22 v) = ρ w31 v := by
  apply difference_step h (rootElement 0 4) w22 w31
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

include h1 in
private theorem action131 : difference ρ (rootElement 1 4) (ρ w31 v) = ρ w32 v := by
  apply difference_step h (rootElement 1 4) w31 w32
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private theorem action132 : difference ρ (rootElement 1 2) (ρ w28 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w28
    [] (by simp) 0 1 (by decide)
  decide +kernel

private theorem action133 : difference ρ (rootElement 1 2) (ρ w31 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w31
    [] (by simp) 2 3 (by decide)
  decide +kernel

include h3 in
private theorem action134 : difference ρ (rootElement 0 4) (ρ w23 v) = ρ w33 v := by
  apply difference_step h (rootElement 0 4) w23 w33
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h0 in
private theorem action135 : difference ρ (rootElement 1 2) (ρ w33 v) = ρ w28 v := by
  apply difference_step h (rootElement 1 2) w33 w28
    [] [] (by simp) (by simp) 0 h0 <;> decide +kernel

private theorem action136 : difference ρ (rootElement 2 3) (ρ w28 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w28
    [] (by simp) 1 2 (by decide)
  decide +kernel

private theorem action137 : difference ρ (rootElement 2 3) (ρ w31 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w31
    [] (by simp) 3 4 (by decide)
  decide +kernel

private theorem action138 : difference ρ (rootElement 2 3) (ρ w33 v) = 0 := by
  apply difference_zero h (rootElement 2 3) w33
    [] (by simp) 0 2 (by decide)
  decide +kernel

include h3 in
private theorem action139 : difference ρ (rootElement 0 4) (ρ w24 v) = ρ w34 v := by
  apply difference_step h (rootElement 0 4) w24 w34
    [] [] (by simp) (by simp) 3 h3 <;> decide +kernel

include h1 in
private theorem action140 : difference ρ (rootElement 2 3) (ρ w34 v) = ρ w28 v := by
  apply difference_step h (rootElement 2 3) w34 w28
    [] [] (by simp) (by simp) 1 h1 <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V)
    (v : V) : Fin 25 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v, ρ w11 v, ρ w12 v, ρ w13 v, ρ w14 v, ρ w15 v, ρ w16 v, ρ w17 v, ρ w18 v, ρ w19 v, ρ w20 v, ρ w21 v, ρ w22 v, ρ w23 v, ρ w24 v]
private def extractors (ρ : Representation (ZMod 2) Representation.SL5TenDimensional.Group V) :
    Fin 25 → V →ₗ[ZMod 2] V :=
  ![
    LinearMap.id,
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 1 2)).comp (LinearMap.id),
    (difference ρ (rootElement 3 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp (LinearMap.id),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp (LinearMap.id),
    (difference ρ (rootElement 2 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp ((difference ρ (rootElement 3 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 3 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 3)).comp (LinearMap.id),
    (difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 0 3)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 1)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 3 4)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id)),
    (difference ρ (rootElement 3 4)).comp ((difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 2)).comp (LinearMap.id))),
    (difference ρ (rootElement 0 4)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 1 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 0 3)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 3)).comp ((difference ρ (rootElement 0 3)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id))),
    (difference ρ (rootElement 1 4)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 2)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 3)).comp ((difference ρ (rootElement 0 4)).comp (LinearMap.id))]
omit h in

private theorem kills0 (j : Fin 25) (hj : j.val < 0) :
    extractors ρ 0 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj

private theorem kills1 (j : Fin 25) (hj : j.val < 1) :
    extractors ρ 1 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
    simp only [action0 h]

private theorem kills2 (j : Fin 25) (hj : j.val < 2) :
    extractors ρ 2 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (ρ w0 v) = 0
    simp only [action2 h]
  · change difference ρ (rootElement 1 2) (ρ w1 v) = 0
    simp only [action3 h]

private theorem kills3 (j : Fin 25) (hj : j.val < 3) :
    extractors ρ 3 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 3 4) (ρ w0 v) = 0
    simp only [action5 h]
  · change difference ρ (rootElement 3 4) (ρ w1 v) = 0
    simp only [action6 h]
  · change difference ρ (rootElement 3 4) (ρ w2 v) = 0
    simp only [action7 h]

private theorem kills4 (j : Fin 25) (hj : j.val < 4) :
    extractors ρ 4 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 2) (ρ w0 v) = 0
    simp only [action9 h]
  · change difference ρ (rootElement 0 2) (ρ w1 v) = 0
    simp only [action10 h]
  · change difference ρ (rootElement 0 2) (ρ w2 v) = 0
    simp only [action11 h]
  · change difference ρ (rootElement 0 2) (ρ w3 v) = 0
    simp only [action12 h]
include h1 in

private theorem kills5 (j : Fin 25) (hj : j.val < 5) :
    extractors ρ 5 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
    simp only [action13 h h1, action3 h]

private theorem kills6 (j : Fin 25) (hj : j.val < 6) :
    extractors ρ 6 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 3) (ρ w0 v) = 0
    simp only [action15 h]
  · change difference ρ (rootElement 1 3) (ρ w1 v) = 0
    simp only [action16 h]
  · change difference ρ (rootElement 1 3) (ρ w2 v) = 0
    simp only [action17 h]
  · change difference ρ (rootElement 1 3) (ρ w3 v) = 0
    simp only [action18 h]
  · change difference ρ (rootElement 1 3) (ρ w4 v) = 0
    simp only [action19 h]
  · change difference ρ (rootElement 1 3) (ρ w5 v) = 0
    simp only [action20 h]

private theorem kills7 (j : Fin 25) (hj : j.val < 7) :
    extractors ρ 7 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 4) (ρ w0 v) = 0
    simp only [action22 h]
  · change difference ρ (rootElement 2 4) (ρ w1 v) = 0
    simp only [action23 h]
  · change difference ρ (rootElement 2 4) (ρ w2 v) = 0
    simp only [action24 h]
  · change difference ρ (rootElement 2 4) (ρ w3 v) = 0
    simp only [action25 h]
  · change difference ρ (rootElement 2 4) (ρ w4 v) = 0
    simp only [action26 h]
  · change difference ρ (rootElement 2 4) (ρ w5 v) = 0
    simp only [action27 h]
  · change difference ρ (rootElement 2 4) (ρ w6 v) = 0
    simp only [action28 h]
include h3 in

private theorem kills8 (j : Fin 25) (hj : j.val < 8) :
    extractors ρ 8 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w0 v)) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w1 v)) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w2 v)) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w3 v)) = 0
    simp only [action8 h h3, action0 h]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w4 v)) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w5 v)) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w6 v)) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w7 v)) = 0
    simp only [action33 h, map_zero]
include h3 in

private theorem kills9 (j : Fin 25) (hj : j.val < 9) :
    extractors ρ 9 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w0 v)) = 0
    simp only [action5 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w1 v)) = 0
    simp only [action6 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w2 v)) = 0
    simp only [action7 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w3 v)) = 0
    simp only [action8 h h3, action2 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w4 v)) = 0
    simp only [action30 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w5 v)) = 0
    simp only [action31 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w6 v)) = 0
    simp only [action32 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w7 v)) = 0
    simp only [action33 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w8 v)) = 0
    simp only [action34 h h3, action3 h]

private theorem kills10 (j : Fin 25) (hj : j.val < 10) :
    extractors ρ 10 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
    simp only [action36 h]
  · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
    simp only [action37 h]
  · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
    simp only [action38 h]
  · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
    simp only [action39 h]
  · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
    simp only [action40 h]
  · change difference ρ (rootElement 1 4) (ρ w5 v) = 0
    simp only [action41 h]
  · change difference ρ (rootElement 1 4) (ρ w6 v) = 0
    simp only [action42 h]
  · change difference ρ (rootElement 1 4) (ρ w7 v) = 0
    simp only [action43 h]
  · change difference ρ (rootElement 1 4) (ρ w8 v) = 0
    simp only [action44 h]
  · change difference ρ (rootElement 1 4) (ρ w9 v) = 0
    simp only [action45 h]

private theorem kills11 (j : Fin 25) (hj : j.val < 11) :
    extractors ρ 11 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 3) (ρ w0 v) = 0
    simp only [action47 h]
  · change difference ρ (rootElement 0 3) (ρ w1 v) = 0
    simp only [action48 h]
  · change difference ρ (rootElement 0 3) (ρ w2 v) = 0
    simp only [action49 h]
  · change difference ρ (rootElement 0 3) (ρ w3 v) = 0
    simp only [action50 h]
  · change difference ρ (rootElement 0 3) (ρ w4 v) = 0
    simp only [action51 h]
  · change difference ρ (rootElement 0 3) (ρ w5 v) = 0
    simp only [action52 h]
  · change difference ρ (rootElement 0 3) (ρ w6 v) = 0
    simp only [action53 h]
  · change difference ρ (rootElement 0 3) (ρ w7 v) = 0
    simp only [action54 h]
  · change difference ρ (rootElement 0 3) (ρ w8 v) = 0
    simp only [action55 h]
  · change difference ρ (rootElement 0 3) (ρ w9 v) = 0
    simp only [action56 h]
  · change difference ρ (rootElement 0 3) (ρ w10 v) = 0
    simp only [action57 h]
include h1 in

private theorem kills12 (j : Fin 25) (hj : j.val < 12) :
    extractors ρ 12 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w0 v)) = 0
    simp only [action47 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w1 v)) = 0
    simp only [action48 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w2 v)) = 0
    simp only [action49 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w3 v)) = 0
    simp only [action50 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w4 v)) = 0
    simp only [action51 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w5 v)) = 0
    simp only [action52 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w6 v)) = 0
    simp only [action53 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w7 v)) = 0
    simp only [action54 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w8 v)) = 0
    simp only [action55 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w9 v)) = 0
    simp only [action56 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w10 v)) = 0
    simp only [action57 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w11 v)) = 0
    simp only [action58 h h1, action59 h]
include h3 in

private theorem kills13 (j : Fin 25) (hj : j.val < 13) :
    extractors ρ 13 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w0 v)) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w1 v)) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w2 v)) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w3 v)) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w4 v)) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w5 v)) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w6 v)) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w7 v)) = 0
    simp only [action29 h h3, action61 h]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w8 v)) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w9 v)) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w10 v)) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w11 v)) = 0
    simp only [action65 h, map_zero]
  · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w12 v)) = 0
    simp only [action66 h, map_zero]
include h3 in

private theorem kills14 (j : Fin 25) (hj : j.val < 14) :
    extractors ρ 14 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w0 v)) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w1 v)) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w2 v)) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w3 v)) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w4 v)) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w5 v)) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w6 v)) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w7 v)) = 0
    simp only [action29 h h3, action69 h]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w8 v)) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w9 v)) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w10 v)) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w11 v)) = 0
    simp only [action65 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w12 v)) = 0
    simp only [action66 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w13 v)) = 0
    simp only [action67 h h3, action59 h]
include h0 h1 in

private theorem kills15 (j : Fin 25) (hj : j.val < 15) :
    extractors ρ 15 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w0 v)) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w1 v)) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w2 v)) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w3 v)) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w4 v)) = 0
    simp only [action13 h h1, action6 h]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w5 v)) = 0
    simp only [action14 h h0, action7 h]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w6 v)) = 0
    simp only [action71 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w7 v)) = 0
    simp only [action72 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w8 v)) = 0
    simp only [action73 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w9 v)) = 0
    simp only [action74 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w10 v)) = 0
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w11 v)) = 0
    simp only [action76 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w12 v)) = 0
    simp only [action77 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w13 v)) = 0
    simp only [action78 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w14 v)) = 0
    simp only [action79 h, map_zero]
include h0 h1 in

private theorem kills16 (j : Fin 25) (hj : j.val < 16) :
    extractors ρ 16 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w0 v))) = 0
    simp only [action9 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w1 v))) = 0
    simp only [action10 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w2 v))) = 0
    simp only [action11 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w3 v))) = 0
    simp only [action12 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w4 v))) = 0
    simp only [action13 h h1, action3 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w5 v))) = 0
    simp only [action14 h h0, action4 h h1, action5 h]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w6 v))) = 0
    simp only [action71 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w7 v))) = 0
    simp only [action72 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w8 v))) = 0
    simp only [action73 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w9 v))) = 0
    simp only [action74 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w10 v))) = 0
    simp only [action75 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w11 v))) = 0
    simp only [action76 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w12 v))) = 0
    simp only [action77 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w13 v))) = 0
    simp only [action78 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w14 v))) = 0
    simp only [action79 h, map_zero]
  · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w15 v))) = 0
    simp only [action80 h h1, action81 h, map_zero]

private theorem kills17 (j : Fin 25) (hj : j.val < 17) :
    extractors ρ 17 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 4) (ρ w0 v) = 0
    simp only [action84 h]
  · change difference ρ (rootElement 0 4) (ρ w1 v) = 0
    simp only [action85 h]
  · change difference ρ (rootElement 0 4) (ρ w2 v) = 0
    simp only [action86 h]
  · change difference ρ (rootElement 0 4) (ρ w3 v) = 0
    simp only [action87 h]
  · change difference ρ (rootElement 0 4) (ρ w4 v) = 0
    simp only [action88 h]
  · change difference ρ (rootElement 0 4) (ρ w5 v) = 0
    simp only [action89 h]
  · change difference ρ (rootElement 0 4) (ρ w6 v) = 0
    simp only [action90 h]
  · change difference ρ (rootElement 0 4) (ρ w7 v) = 0
    simp only [action91 h]
  · change difference ρ (rootElement 0 4) (ρ w8 v) = 0
    simp only [action92 h]
  · change difference ρ (rootElement 0 4) (ρ w9 v) = 0
    simp only [action93 h]
  · change difference ρ (rootElement 0 4) (ρ w10 v) = 0
    simp only [action94 h]
  · change difference ρ (rootElement 0 4) (ρ w11 v) = 0
    simp only [action95 h]
  · change difference ρ (rootElement 0 4) (ρ w12 v) = 0
    simp only [action96 h]
  · change difference ρ (rootElement 0 4) (ρ w13 v) = 0
    simp only [action97 h]
  · change difference ρ (rootElement 0 4) (ρ w14 v) = 0
    simp only [action98 h]
  · change difference ρ (rootElement 0 4) (ρ w15 v) = 0
    simp only [action99 h]
  · change difference ρ (rootElement 0 4) (ρ w16 v) = 0
    simp only [action100 h]
include h3 in

private theorem kills18 (j : Fin 25) (hj : j.val < 18) :
    extractors ρ 18 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
    simp only [action36 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
    simp only [action37 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
    simp only [action38 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
    simp only [action39 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
    simp only [action40 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
    simp only [action41 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
    simp only [action42 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
    simp only [action43 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
    simp only [action44 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
    simp only [action45 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w10 v)) = 0
    simp only [action46 h h3, action102 h]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w11 v)) = 0
    simp only [action103 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w12 v)) = 0
    simp only [action104 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w13 v)) = 0
    simp only [action105 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w14 v)) = 0
    simp only [action106 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w15 v)) = 0
    simp only [action107 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w16 v)) = 0
    simp only [action108 h, map_zero]
  · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w17 v)) = 0
    simp only [action109 h, map_zero]
include h3 in

private theorem kills19 (j : Fin 25) (hj : j.val < 19) :
    extractors ρ 19 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w0 v)) = 0
    simp only [action36 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w1 v)) = 0
    simp only [action37 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w2 v)) = 0
    simp only [action38 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w3 v)) = 0
    simp only [action39 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w4 v)) = 0
    simp only [action40 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w5 v)) = 0
    simp only [action41 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w6 v)) = 0
    simp only [action42 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w7 v)) = 0
    simp only [action43 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w8 v)) = 0
    simp only [action44 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w9 v)) = 0
    simp only [action45 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w10 v)) = 0
    simp only [action46 h h3, action112 h]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w11 v)) = 0
    simp only [action103 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w12 v)) = 0
    simp only [action104 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w13 v)) = 0
    simp only [action105 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w14 v)) = 0
    simp only [action106 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w15 v)) = 0
    simp only [action107 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w16 v)) = 0
    simp only [action108 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w17 v)) = 0
    simp only [action109 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w18 v)) = 0
    simp only [action110 h h3, action113 h]
include h3 in

private theorem kills20 (j : Fin 25) (hj : j.val < 20) :
    extractors ρ 20 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w0 v)) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w1 v)) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w2 v)) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w3 v)) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w4 v)) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w5 v)) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w6 v)) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w7 v)) = 0
    simp only [action29 h h3, action116 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w8 v)) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w9 v)) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w10 v)) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w11 v)) = 0
    simp only [action65 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w12 v)) = 0
    simp only [action66 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w13 v)) = 0
    simp only [action67 h h3, action117 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w14 v)) = 0
    simp only [action70 h h3, action53 h]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w15 v)) = 0
    simp only [action118 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w16 v)) = 0
    simp only [action119 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w17 v)) = 0
    simp only [action120 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w18 v)) = 0
    simp only [action121 h, map_zero]
  · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w19 v)) = 0
    simp only [action122 h, map_zero]
include h1 h3 in

private theorem kills21 (j : Fin 25) (hj : j.val < 21) :
    extractors ρ 21 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w0 v))) = 0
    simp only [action22 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w1 v))) = 0
    simp only [action23 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w2 v))) = 0
    simp only [action24 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w3 v))) = 0
    simp only [action25 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w4 v))) = 0
    simp only [action26 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w5 v))) = 0
    simp only [action27 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w6 v))) = 0
    simp only [action28 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w7 v))) = 0
    simp only [action29 h h3, action116 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w8 v))) = 0
    simp only [action62 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w9 v))) = 0
    simp only [action63 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w10 v))) = 0
    simp only [action64 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w11 v))) = 0
    simp only [action65 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w12 v))) = 0
    simp only [action66 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w13 v))) = 0
    simp only [action67 h h3, action117 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w14 v))) = 0
    simp only [action70 h h3, action53 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w15 v))) = 0
    simp only [action118 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w16 v))) = 0
    simp only [action119 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w17 v))) = 0
    simp only [action120 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w18 v))) = 0
    simp only [action121 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w19 v))) = 0
    simp only [action122 h, map_zero]
  · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w20 v))) = 0
    simp only [action123 h h3, action58 h h1, action59 h]
include h3 in

private theorem kills22 (j : Fin 25) (hj : j.val < 22) :
    extractors ρ 22 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    simp only [action88 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    simp only [action89 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    simp only [action91 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    simp only [action92 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    simp only [action93 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    simp only [action94 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    simp only [action95 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    simp only [action96 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    simp only [action97 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    simp only [action98 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    simp only [action99 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    simp only [action100 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    simp only [action101 h h3, action125 h]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w18 v)) = 0
    simp only [action126 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    simp only [action127 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    simp only [action128 h, map_zero]
  · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    simp only [action129 h, map_zero]
include h0 h3 in

private theorem kills23 (j : Fin 25) (hj : j.val < 23) :
    extractors ρ 23 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    simp only [action88 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    simp only [action89 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    simp only [action91 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    simp only [action92 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    simp only [action93 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    simp only [action94 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    simp only [action95 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    simp only [action96 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    simp only [action97 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    simp only [action98 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    simp only [action99 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    simp only [action100 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    simp only [action101 h h3, action132 h]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w18 v)) = 0
    simp only [action126 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    simp only [action127 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    simp only [action128 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    simp only [action129 h, map_zero]
  · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w22 v)) = 0
    simp only [action130 h h0, action133 h]
include h0 h3 in

private theorem kills24 (j : Fin 25) (hj : j.val < 24) :
    extractors ρ 24 (vectors ρ v j) = 0 := by
  fin_cases j <;> norm_num at hj
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w0 v)) = 0
    simp only [action84 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w1 v)) = 0
    simp only [action85 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w2 v)) = 0
    simp only [action86 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w3 v)) = 0
    simp only [action87 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w4 v)) = 0
    simp only [action88 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w5 v)) = 0
    simp only [action89 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w6 v)) = 0
    simp only [action90 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w7 v)) = 0
    simp only [action91 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w8 v)) = 0
    simp only [action92 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w9 v)) = 0
    simp only [action93 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w10 v)) = 0
    simp only [action94 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w11 v)) = 0
    simp only [action95 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w12 v)) = 0
    simp only [action96 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w13 v)) = 0
    simp only [action97 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w14 v)) = 0
    simp only [action98 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w15 v)) = 0
    simp only [action99 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w16 v)) = 0
    simp only [action100 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w17 v)) = 0
    simp only [action101 h h3, action136 h]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w18 v)) = 0
    simp only [action126 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w19 v)) = 0
    simp only [action127 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w20 v)) = 0
    simp only [action128 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w21 v)) = 0
    simp only [action129 h, map_zero]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w22 v)) = 0
    simp only [action130 h h0, action137 h]
  · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w23 v)) = 0
    simp only [action134 h h3, action138 h]
include h0 h1 h3 in

private theorem independent (hv : v ≠ 0) :
    LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i
    · exact kills0 j hij
    · exact kills1 h j hij
    · exact kills2 h j hij
    · exact kills3 h j hij
    · exact kills4 h j hij
    · exact kills5 h h1 j hij
    · exact kills6 h j hij
    · exact kills7 h j hij
    · exact kills8 h h3 j hij
    · exact kills9 h h3 j hij
    · exact kills10 h j hij
    · exact kills11 h j hij
    · exact kills12 h h1 j hij
    · exact kills13 h h3 j hij
    · exact kills14 h h3 j hij
    · exact kills15 h h0 h1 j hij
    · exact kills16 h h0 h1 j hij
    · exact kills17 h j hij
    · exact kills18 h h3 j hij
    · exact kills19 h h3 j hij
    · exact kills20 h h3 j hij
    · exact kills21 h h1 h3 j hij
    · exact kills22 h h3 j hij
    · exact kills23 h h0 h3 j hij
    · exact kills24 h h0 h3 j hij
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w1 v) ≠ 0
      rw [action1 h h0]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (ρ w2 v) ≠ 0
      rw [action4 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (ρ w3 v) ≠ 0
      rw [action8 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (ρ w4 v) ≠ 0
      rw [action13 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w5 v)) ≠ 0
      rw [action14 h h0, action4 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (ρ w6 v) ≠ 0
      rw [action21 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (ρ w7 v) ≠ 0
      rw [action29 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 3 4) (ρ w8 v)) ≠ 0
      rw [action34 h h3, action1 h h0]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 3 4) (ρ w9 v)) ≠ 0
      rw [action35 h h3, action4 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w10 v) ≠ 0
      rw [action46 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (ρ w11 v) ≠ 0
      rw [action58 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (ρ w12 v)) ≠ 0
      rw [action60 h h0, action21 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (difference ρ (rootElement 2 4) (ρ w13 v)) ≠ 0
      rw [action67 h h3, action68 h h0]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (difference ρ (rootElement 2 4) (ρ w14 v)) ≠ 0
      rw [action70 h h3, action21 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 2) (ρ w15 v)) ≠ 0
      rw [action80 h h1, action34 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 1 2) (difference ρ (rootElement 0 2) (ρ w16 v))) ≠ 0
      rw [action82 h h0, action83 h h1, action8 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 4) (ρ w17 v) ≠ 0
      rw [action101 h h3]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (difference ρ (rootElement 1 4) (ρ w18 v)) ≠ 0
      rw [action110 h h3, action111 h h0]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 1 4) (ρ w19 v)) ≠ 0
      rw [action114 h h3, action115 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w20 v)) ≠ 0
      rw [action123 h h3, action58 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 3) (difference ρ (rootElement 0 3) (difference ρ (rootElement 2 4) (ρ w21 v))) ≠ 0
      rw [action124 h h3, action60 h h0, action21 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (difference ρ (rootElement 0 4) (ρ w22 v)) ≠ 0
      rw [action130 h h0, action131 h h1]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (difference ρ (rootElement 0 4) (ρ w23 v)) ≠ 0
      rw [action134 h h3, action135 h h0]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 3) (difference ρ (rootElement 0 4) (ρ w24 v)) ≠ 0
      rw [action139 h h3, action140 h h1]
      exact translate_ne_zero ρ _ hv
include h0 h1 h3 in

/-- Three specified active roots force dimension at least twenty-five. -/
theorem finrank_ge_twentyFive [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    25 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h h0 h1 h3 hv).fintype_card_le_finrank

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension.Three013
