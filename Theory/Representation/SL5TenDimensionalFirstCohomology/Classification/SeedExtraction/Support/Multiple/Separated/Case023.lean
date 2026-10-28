module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction

/-!
# Eleven translates for support `{0, 2, 3}`

The exchange words below represent permutations of the coordinate blocks cut
at the active roots. The `action*` identities use inactive exchanges to bring
a conjugated transvection either to an upper root (difference zero) or to an
active simple lower root (difference an exchange translate). All matrix
identities are verified by kernel reduction.

The eleven coefficient extractors are triangular: each kills the preceding
vectors and maps its own vector to a nonzero permutation translate. Applying
`linearIndependent_of_triangular` gives the dimension bound. This certificate
uses only the local highest-vector relations, with no irreducibility assumption.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

open Representation.SL5TenDimensional.Classification
namespace Representation.SL5TenDimensional.Classification.Separated.Case023
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {0, 2, 3} v)
include h

private def w0 : Group := swapWord []
private def w1 : Group := swapWord [2]
private def w2 : Group := swapWord [0]
private def w3 : Group := swapWord [3]
private def w4 : Group := swapWord [3, 2]
private def w5 : Group := swapWord [1, 2]
private def w6 : Group := swapWord [1, 0]
private def w7 : Group := swapWord [2, 3]
private def w8 : Group := swapWord [3, 0]
private def w9 : Group := swapWord [2, 0]
private def w10 : Group := swapWord [3, 1, 2]
private theorem action0 : difference ρ (rootElement 2 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w0
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action1 : difference ρ (rootElement 2 1) (ρ w1 v) = ρ w5 v := by
  apply difference_step h (rootElement 2 1) w1 w5
    [1] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action2 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action3 : difference ρ (rootElement 0 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action4 : difference ρ (rootElement 0 1) (ρ w2 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 1) w2 w0
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action5 : difference ρ (rootElement 3 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w0
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action6 : difference ρ (rootElement 3 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w1
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action7 : difference ρ (rootElement 3 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 3 4) w2
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action8 : difference ρ (rootElement 3 4) (ρ w3 v) = ρ w0 v := by
  apply difference_step h (rootElement 3 4) w3 w0
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action9 : difference ρ (rootElement 2 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w0
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action10 : difference ρ (rootElement 2 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w1
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action11 : difference ρ (rootElement 2 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w2
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action12 : difference ρ (rootElement 2 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w3
    [] (by decide +kernel) 2 3 (by decide +kernel)
  decide +kernel

private theorem action13 : difference ρ (rootElement 2 4) (ρ w4 v) = ρ w3 v := by
  apply difference_step h (rootElement 2 4) w4 w3
    [] [] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action14 : difference ρ (rootElement 1 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w0
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action15 : difference ρ (rootElement 1 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w1
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action16 : difference ρ (rootElement 1 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w2
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action17 : difference ρ (rootElement 1 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w3
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action18 : difference ρ (rootElement 1 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 2) w4
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action19 : difference ρ (rootElement 1 2) (ρ w5 v) = ρ w1 v := by
  apply difference_step h (rootElement 1 2) w5 w1
    [1] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private theorem action20 : difference ρ (rootElement 0 2) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w0
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action21 : difference ρ (rootElement 0 2) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w1
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action22 : difference ρ (rootElement 0 2) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w2
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action23 : difference ρ (rootElement 0 2) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w3
    [] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action24 : difference ρ (rootElement 0 2) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w4
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action25 : difference ρ (rootElement 0 2) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 2) w5
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action26 : difference ρ (rootElement 0 2) (ρ w6 v) = ρ w0 v := by
  apply difference_step h (rootElement 0 2) w6 w0
    [] [1] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action27 : difference ρ (rootElement 2 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 2 1) w3
    [1] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action28 : difference ρ (rootElement 2 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w5
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action29 : difference ρ (rootElement 2 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 2 4) w6
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action30 : difference ρ (rootElement 2 4) (ρ w7 v) = ρ w1 v := by
  apply difference_step h (rootElement 2 4) w7 w1
    [] [] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action31 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action32 : difference ρ (rootElement 0 1) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w4
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action33 : difference ρ (rootElement 0 1) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w5
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action34 : difference ρ (rootElement 0 1) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w6
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action35 : difference ρ (rootElement 0 1) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w7
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action36 : difference ρ (rootElement 0 1) (ρ w8 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 1) w8 w3
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action37 : difference ρ (rootElement 0 1) (ρ w9 v) = ρ w1 v := by
  apply difference_step h (rootElement 0 1) w9 w1
    [] [] (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) <;> decide +kernel

private theorem action38 : difference ρ (rootElement 1 4) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w0
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action39 : difference ρ (rootElement 1 4) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w1
    [] (by decide +kernel) 1 4 (by decide +kernel)
  decide +kernel

private theorem action40 : difference ρ (rootElement 1 4) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w2
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action41 : difference ρ (rootElement 1 4) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w3
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action42 : difference ρ (rootElement 1 4) (ρ w4 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w4
    [] (by decide +kernel) 1 2 (by decide +kernel)
  decide +kernel

private theorem action43 : difference ρ (rootElement 1 4) (ρ w5 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w5
    [] (by decide +kernel) 3 4 (by decide +kernel)
  decide +kernel

private theorem action44 : difference ρ (rootElement 1 4) (ρ w6 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w6
    [] (by decide +kernel) 2 4 (by decide +kernel)
  decide +kernel

private theorem action45 : difference ρ (rootElement 1 4) (ρ w7 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w7
    [] (by decide +kernel) 1 3 (by decide +kernel)
  decide +kernel

private theorem action46 : difference ρ (rootElement 1 4) (ρ w8 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w8
    [] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action47 : difference ρ (rootElement 1 4) (ρ w9 v) = 0 := by
  apply difference_zero h (rootElement 1 4) w9
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action48 : difference ρ (rootElement 1 4) (ρ w10 v) = ρ w3 v := by
  apply difference_step h (rootElement 1 4) w10 w3
    [] [1] (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 11 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v, ρ w5 v, ρ w6 v, ρ w7 v, ρ w8 v, ρ w9 v, ρ w10 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 11 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 2 1)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp (LinearMap.id),
    (difference ρ (rootElement 3 4)).comp (LinearMap.id),
    (difference ρ (rootElement 2 4)).comp (LinearMap.id),
    (difference ρ (rootElement 1 2)).comp (LinearMap.id),
    (difference ρ (rootElement 0 2)).comp (LinearMap.id),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 2 4)).comp (LinearMap.id)),
    (difference ρ (rootElement 3 4)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 2 1)).comp ((difference ρ (rootElement 0 1)).comp (LinearMap.id)),
    (difference ρ (rootElement 1 4)).comp (LinearMap.id)]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference ρ (rootElement 2 1) (ρ w0 v) = 0
      rw [action0 h]
    · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
      rw [action2 h]
    · change difference ρ (rootElement 0 1) (ρ w1 v) = 0
      rw [action3 h]
    · change difference ρ (rootElement 3 4) (ρ w0 v) = 0
      rw [action5 h]
    · change difference ρ (rootElement 3 4) (ρ w1 v) = 0
      rw [action6 h]
    · change difference ρ (rootElement 3 4) (ρ w2 v) = 0
      rw [action7 h]
    · change difference ρ (rootElement 2 4) (ρ w0 v) = 0
      rw [action9 h]
    · change difference ρ (rootElement 2 4) (ρ w1 v) = 0
      rw [action10 h]
    · change difference ρ (rootElement 2 4) (ρ w2 v) = 0
      rw [action11 h]
    · change difference ρ (rootElement 2 4) (ρ w3 v) = 0
      rw [action12 h]
    · change difference ρ (rootElement 1 2) (ρ w0 v) = 0
      rw [action14 h]
    · change difference ρ (rootElement 1 2) (ρ w1 v) = 0
      rw [action15 h]
    · change difference ρ (rootElement 1 2) (ρ w2 v) = 0
      rw [action16 h]
    · change difference ρ (rootElement 1 2) (ρ w3 v) = 0
      rw [action17 h]
    · change difference ρ (rootElement 1 2) (ρ w4 v) = 0
      rw [action18 h]
    · change difference ρ (rootElement 0 2) (ρ w0 v) = 0
      rw [action20 h]
    · change difference ρ (rootElement 0 2) (ρ w1 v) = 0
      rw [action21 h]
    · change difference ρ (rootElement 0 2) (ρ w2 v) = 0
      rw [action22 h]
    · change difference ρ (rootElement 0 2) (ρ w3 v) = 0
      rw [action23 h]
    · change difference ρ (rootElement 0 2) (ρ w4 v) = 0
      rw [action24 h]
    · change difference ρ (rootElement 0 2) (ρ w5 v) = 0
      rw [action25 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w0 v)) = 0
      rw [action9 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w1 v)) = 0
      rw [action10 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w2 v)) = 0
      rw [action11 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w3 v)) = 0
      rw [action12 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w4 v)) = 0
      rw [action13 h, action27 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w5 v)) = 0
      rw [action28 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w6 v)) = 0
      rw [action29 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
      rw [action2 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
      rw [action3 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
      rw [action4 h, action5 h]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
      rw [action31 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
      rw [action32 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
      rw [action33 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
      rw [action34 h, map_zero]
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
      rw [action35 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w0 v)) = 0
      rw [action2 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w1 v)) = 0
      rw [action3 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w2 v)) = 0
      rw [action4 h, action0 h]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w3 v)) = 0
      rw [action31 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w4 v)) = 0
      rw [action32 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w5 v)) = 0
      rw [action33 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w6 v)) = 0
      rw [action34 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w7 v)) = 0
      rw [action35 h, map_zero]
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w8 v)) = 0
      rw [action36 h, action27 h]
    · change difference ρ (rootElement 1 4) (ρ w0 v) = 0
      rw [action38 h]
    · change difference ρ (rootElement 1 4) (ρ w1 v) = 0
      rw [action39 h]
    · change difference ρ (rootElement 1 4) (ρ w2 v) = 0
      rw [action40 h]
    · change difference ρ (rootElement 1 4) (ρ w3 v) = 0
      rw [action41 h]
    · change difference ρ (rootElement 1 4) (ρ w4 v) = 0
      rw [action42 h]
    · change difference ρ (rootElement 1 4) (ρ w5 v) = 0
      rw [action43 h]
    · change difference ρ (rootElement 1 4) (ρ w6 v) = 0
      rw [action44 h]
    · change difference ρ (rootElement 1 4) (ρ w7 v) = 0
      rw [action45 h]
    · change difference ρ (rootElement 1 4) (ρ w8 v) = 0
      rw [action46 h]
    · change difference ρ (rootElement 1 4) (ρ w9 v) = 0
      rw [action47 h]
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 4) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 2) (ρ w5 v) ≠ 0
      rw [action19 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 2) (ρ w6 v) ≠ 0
      rw [action26 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 2 4) (ρ w7 v)) ≠ 0
      rw [action30 h, action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 4) (difference ρ (rootElement 0 1) (ρ w8 v)) ≠ 0
      rw [action36 h, action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 1) (difference ρ (rootElement 0 1) (ρ w9 v)) ≠ 0
      rw [action37 h, action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 4) (ρ w10 v) ≠ 0
      rw [action48 h]
      exact translate_ne_zero ρ _ hv

/-- Eleven independent translates give the dimension bound for this support. -/
theorem eleven_le [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    11 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank
end Representation.SL5TenDimensional.Classification.Separated.Case023
