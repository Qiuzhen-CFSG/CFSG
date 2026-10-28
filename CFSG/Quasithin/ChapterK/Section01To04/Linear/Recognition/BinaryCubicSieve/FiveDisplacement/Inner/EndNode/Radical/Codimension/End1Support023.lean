module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.Certificate
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Nine cosets for end 1 and support `{0, 2, 3}`

Each root action follows from the local highest-vector relations, with
finite matrix identities checked by kernel reduction. The nine extracting
operators kill the common fixed space because their first applied root
lies in the marked radical. Their triangular action proves independence
of nine cosets, and hence fixed codimension at least nine.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.7 step 1, pp.25–26; Aschbacher–Smith K.3.2, pp.454–455.
-/

public section
open Representation Representation.BinaryOffender
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension.End1Support023
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) SL5TenDimensional.Group V} {v : V}

private def permutationElement (p : Equiv.Perm (Fin 5)) : SL5TenDimensional.Group :=
  ⟨p.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> rw [hp] <;> decide⟩

private def w0 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 3, 2, 0], ![4, 0, 3, 2, 1], by decide +kernel, by decide +kernel⟩

private def w1 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 4, 3, 1, 2], ![0, 3, 4, 2, 1], by decide +kernel, by decide +kernel⟩

private def w2 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], by decide +kernel, by decide +kernel⟩

private def w3 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 4, 3, 2], ![0, 1, 4, 3, 2], by decide +kernel, by decide +kernel⟩

private def w4 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 4, 1, 0, 2], ![3, 2, 4, 0, 1], by decide +kernel, by decide +kernel⟩

private def w5 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 2, 0, 3], ![3, 0, 2, 4, 1], by decide +kernel, by decide +kernel⟩

private def w6 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 4, 1, 2, 3], ![0, 2, 3, 4, 1], by decide +kernel, by decide +kernel⟩

private def w7 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 1, 4, 0, 2], ![3, 1, 4, 0, 2], by decide +kernel, by decide +kernel⟩

private def w8 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 4, 0, 3], ![3, 0, 1, 4, 2], by decide +kernel, by decide +kernel⟩

private def w9 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 3, 4, 0, 2], ![3, 0, 4, 1, 2], by decide +kernel, by decide +kernel⟩

private def w10 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 1, 0, 4, 2], ![2, 1, 4, 0, 3], by decide +kernel, by decide +kernel⟩

private def w11 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 2, 0, 4, 3], ![2, 0, 1, 4, 3], by decide +kernel, by decide +kernel⟩

private def w12 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide +kernel, by decide +kernel⟩

private def w13 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 4, 0, 1, 2], ![2, 3, 4, 0, 1], by decide +kernel, by decide +kernel⟩

private def w14 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 4, 0, 2, 3], ![2, 0, 3, 4, 1], by decide +kernel, by decide +kernel⟩

private def w15 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 3, 1, 2, 4], ![0, 2, 3, 1, 4], by decide +kernel, by decide +kernel⟩

private def w16 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 0, 1, 4, 2], ![1, 2, 4, 0, 3], by decide +kernel, by decide +kernel⟩

private def w17 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], by decide +kernel, by decide +kernel⟩

private def w18 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 0, 4, 1, 2], ![1, 3, 4, 0, 2], by decide +kernel, by decide +kernel⟩

private def w19 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 0, 4, 2, 3], ![1, 0, 3, 4, 2], by decide +kernel, by decide +kernel⟩

private def w20 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide +kernel, by decide +kernel⟩

private def w21 : SL5TenDimensional.Group :=
  permutationElement ⟨![0, 1, 3, 2, 4], ![0, 1, 3, 2, 4], by decide +kernel, by decide +kernel⟩

private def w22 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 1, 2, 0, 3], ![3, 1, 2, 4, 0], by decide +kernel, by decide +kernel⟩

private def w23 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 1, 2, 0, 4], ![3, 1, 2, 0, 4], by decide +kernel, by decide +kernel⟩

private def w24 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide +kernel, by decide +kernel⟩

private def w25 : SL5TenDimensional.Group :=
  permutationElement ⟨![4, 1, 0, 2, 3], ![2, 1, 3, 4, 0], by decide +kernel, by decide +kernel⟩

private def w26 : SL5TenDimensional.Group :=
  permutationElement ⟨![3, 1, 0, 2, 4], ![2, 1, 3, 0, 4], by decide +kernel, by decide +kernel⟩

private def w27 : SL5TenDimensional.Group :=
  permutationElement ⟨![1, 3, 0, 2, 4], ![2, 0, 3, 1, 4], by decide +kernel, by decide +kernel⟩

private theorem action0 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w0 v) = σ w1 v := by
  apply difference_step h (rootElement 0 4) w0 w1
    [] [1]
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action1 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 1 2) (σ w1 v) = σ w2 v := by
  apply difference_step h (rootElement 1 2) w1 w2
    [] []
    (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action2 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 1 3) (σ w2 v) = σ w3 v := by
  apply difference_step h (rootElement 1 3) w2 w3
    [1] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action3 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 3) (σ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w1
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action4 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w4 v) = σ w5 v := by
  apply difference_step h (rootElement 0 4) w4 w5
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action5 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 3) (σ w5 v) = σ w6 v := by
  apply difference_step h (rootElement 0 3) w5 w6
    [] [1]
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action6 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 4 1) (σ w1 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w1
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action7 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 4 1) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 4 1) w5
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action8 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w7 v) = σ w8 v := by
  apply difference_step h (rootElement 0 4) w7 w8
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action9 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 4 1) (σ w8 v) = σ w9 v := by
  apply difference_step h (rootElement 4 1) w8 w9
    [] []
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action10 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action11 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action12 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w8
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action13 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w10 v) = σ w11 v := by
  apply difference_step h (rootElement 0 4) w10 w11
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action14 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w11 v) = σ w12 v := by
  apply difference_step h (rootElement 0 2) w11 w12
    [] [1]
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action15 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 1 4) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w12
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action16 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w13 v) = σ w14 v := by
  apply difference_step h (rootElement 0 4) w13 w14
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action17 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w14 v) = σ w6 v := by
  apply difference_step h (rootElement 0 2) w14 w6
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action18 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 1 4) (σ w6 v) = σ w15 v := by
  apply difference_step h (rootElement 1 4) w6 w15
    [] []
    (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action19 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action20 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w5
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action21 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w8 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w8
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action22 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w11 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w11
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action23 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w14 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w14
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action24 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w16 v) = σ w17 v := by
  apply difference_step h (rootElement 0 4) w16 w17
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action25 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w17 v) = σ w12 v := by
  apply difference_step h (rootElement 0 1) w17 w12
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action26 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 2 4) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w12
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action27 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w18 v) = σ w19 v := by
  apply difference_step h (rootElement 0 4) w18 w19
    [] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action28 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w19 v) = σ w20 v := by
  apply difference_step h (rootElement 0 1) w19 w20
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action29 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 2 4) (σ w20 v) = σ w21 v := by
  apply difference_step h (rootElement 2 4) w20 w21
    [] []
    (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action30 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 3) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w12
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action31 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 3) (σ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 3) w20
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action32 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w22 v) = σ w23 v := by
  apply difference_step h (rootElement 0 4) w22 w23
    [] []
    (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action33 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w23 v) = σ w24 v := by
  apply difference_step h (rootElement 0 1) w23 w24
    [1] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action34 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 3) (σ w24 v) = σ w15 v := by
  apply difference_step h (rootElement 0 3) w24 w15
    [] [1]
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action35 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w12 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w12
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action36 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w20 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w20
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action37 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w24 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w24
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action38 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 4) (σ w25 v) = σ w26 v := by
  apply difference_step h (rootElement 0 4) w25 w26
    [] []
    (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action39 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 1) (σ w26 v) = σ w27 v := by
  apply difference_step h (rootElement 0 1) w26 w27
    [1] [1]
    (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action40 (h : LocalHighestVector σ {0, 2, 3} v) :
    difference σ (rootElement 0 2) (σ w27 v) = σ w15 v := by
  apply difference_step h (rootElement 0 2) w27 w15
    [] []
    (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private def vectors (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (v : V) : Fin 9 → V :=
  ![σ w0 v, σ w4 v, σ w7 v, σ w10 v, σ w13 v, σ w16 v, σ w18 v, σ w22 v, σ w25 v]

private def extractors (σ : Representation (ZMod 2) SL5TenDimensional.Group V) :
    Fin 9 → V →ₗ[ZMod 2] V :=
  ![(difference σ (rootElement 1 3)).comp ((difference σ (rootElement 1 2)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id))),
    (difference σ (rootElement 0 3)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id)),
    (difference σ (rootElement 4 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id)),
    (difference σ (rootElement 0 2)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id)),
    (difference σ (rootElement 1 4)).comp ((difference σ (rootElement 0 2)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id))),
    (difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id)),
    (difference σ (rootElement 2 4)).comp ((difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id))),
    (difference σ (rootElement 0 3)).comp ((difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id))),
    (difference σ (rootElement 0 2)).comp ((difference σ (rootElement 0 1)).comp ((difference σ (rootElement 0 4)).comp (LinearMap.id)))]

/-- This support forces nine independent cosets modulo the literal radical fixed space. -/
theorem nine_le_fixedCodim [FiniteDimensional (ZMod 2) V]
    (h : LocalHighestVector σ {0, 2, 3} v) (hv : v ≠ 0) :
    9 ≤ fixedCodim σ (radicalRootGroup 1) := by
  apply fixedCodim_ge_of_triangular σ 1 (vectors σ v) (extractors σ)
  · intro i
    fin_cases i
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 3)).comp ((difference σ (rootElement 1 2)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 3)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 4 1)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 2)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 1 4)).comp ((difference σ (rootElement 0 2)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 1)).comp (LinearMap.id)).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 2 4)).comp ((difference σ (rootElement 0 1)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 3)).comp ((difference σ (rootElement 0 1)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
    · change fixedSpace σ (radicalRootGroup 1) ≤
        LinearMap.ker (((difference σ (rootElement 0 2)).comp ((difference σ (rootElement 0 1)).comp (LinearMap.id))).comp (difference σ (radicalRoot 1 0)))
      exact fixedSpace_le_ker_radical_difference σ 1 0 _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 4) (σ w0 v)) = 0
      rw [action0 h, action3 h]
    · change difference σ (rootElement 4 1) (difference σ (rootElement 0 4) (σ w0 v)) = 0
      rw [action0 h, action6 h]
    · change difference σ (rootElement 4 1) (difference σ (rootElement 0 4) (σ w4 v)) = 0
      rw [action4 h, action7 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w0 v)) = 0
      rw [action0 h, action10 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w4 v)) = 0
      rw [action4 h, action11 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w7 v)) = 0
      rw [action8 h, action12 h]
    · change difference σ (rootElement 1 4) (difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w0 v))) = 0
      rw [action0 h, action10 h, map_zero]
    · change difference σ (rootElement 1 4) (difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w4 v))) = 0
      rw [action4 h, action11 h, map_zero]
    · change difference σ (rootElement 1 4) (difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w7 v))) = 0
      rw [action8 h, action12 h, map_zero]
    · change difference σ (rootElement 1 4) (difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w10 v))) = 0
      rw [action13 h, action14 h, action15 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w0 v)) = 0
      rw [action0 h, action19 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w4 v)) = 0
      rw [action4 h, action20 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w7 v)) = 0
      rw [action8 h, action21 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w10 v)) = 0
      rw [action13 h, action22 h]
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w13 v)) = 0
      rw [action16 h, action23 h]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w0 v))) = 0
      rw [action0 h, action19 h, map_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w4 v))) = 0
      rw [action4 h, action20 h, map_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w7 v))) = 0
      rw [action8 h, action21 h, map_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w10 v))) = 0
      rw [action13 h, action22 h, map_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w13 v))) = 0
      rw [action16 h, action23 h, map_zero]
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w16 v))) = 0
      rw [action24 h, action25 h, action26 h]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w0 v))) = 0
      rw [action0 h, action19 h, map_zero]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w4 v))) = 0
      rw [action4 h, action20 h, map_zero]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w7 v))) = 0
      rw [action8 h, action21 h, map_zero]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w10 v))) = 0
      rw [action13 h, action22 h, map_zero]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w13 v))) = 0
      rw [action16 h, action23 h, map_zero]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w16 v))) = 0
      rw [action24 h, action25 h, action30 h]
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w18 v))) = 0
      rw [action27 h, action28 h, action31 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w0 v))) = 0
      rw [action0 h, action19 h, map_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w4 v))) = 0
      rw [action4 h, action20 h, map_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w7 v))) = 0
      rw [action8 h, action21 h, map_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w10 v))) = 0
      rw [action13 h, action22 h, map_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w13 v))) = 0
      rw [action16 h, action23 h, map_zero]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w16 v))) = 0
      rw [action24 h, action25 h, action35 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w18 v))) = 0
      rw [action27 h, action28 h, action36 h]
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w22 v))) = 0
      rw [action32 h, action33 h, action37 h]
  · intro i
    fin_cases i
    · change difference σ (rootElement 1 3) (difference σ (rootElement 1 2) (difference σ (rootElement 0 4) (σ w0 v))) ≠ 0
      rw [action0 h, action1 h, action2 h]
      exact translate_ne_zero σ w3 hv
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 4) (σ w4 v)) ≠ 0
      rw [action4 h, action5 h]
      exact translate_ne_zero σ w6 hv
    · change difference σ (rootElement 4 1) (difference σ (rootElement 0 4) (σ w7 v)) ≠ 0
      rw [action8 h, action9 h]
      exact translate_ne_zero σ w9 hv
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w10 v)) ≠ 0
      rw [action13 h, action14 h]
      exact translate_ne_zero σ w12 hv
    · change difference σ (rootElement 1 4) (difference σ (rootElement 0 2) (difference σ (rootElement 0 4) (σ w13 v))) ≠ 0
      rw [action16 h, action17 h, action18 h]
      exact translate_ne_zero σ w15 hv
    · change difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w16 v)) ≠ 0
      rw [action24 h, action25 h]
      exact translate_ne_zero σ w12 hv
    · change difference σ (rootElement 2 4) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w18 v))) ≠ 0
      rw [action27 h, action28 h, action29 h]
      exact translate_ne_zero σ w21 hv
    · change difference σ (rootElement 0 3) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w22 v))) ≠ 0
      rw [action32 h, action33 h, action34 h]
      exact translate_ne_zero σ w15 hv
    · change difference σ (rootElement 0 2) (difference σ (rootElement 0 1) (difference σ (rootElement 0 4) (σ w25 v))) ≠ 0
      rw [action38 h, action39 h, action40 h]
      exact translate_ne_zero σ w15 hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension.End1Support023
