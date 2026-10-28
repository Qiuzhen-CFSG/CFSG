module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Extraction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Basic
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Endpoints

/-!
# Dimension certificate for highest-vector support `{3}`

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
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case3
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) Group V} {v : V}
variable (h : LocalHighestVector ρ {3} v)
include h

private def w0 : Group := swapWord []
private def w1 : Group := swapWord [3]
private def w2 : Group := swapWord [2, 3]
private def w3 : Group := swapWord [1, 2, 3]
private def w4 : Group := swapWord [0, 1, 2, 3]
private theorem action0 : difference ρ (rootElement 3 0) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 3 0) w0
    [2, 1, 0, 1, 2] (by decide +kernel) 0 3 (by decide +kernel)
  decide +kernel

private theorem action1 : difference ρ (rootElement 3 0) (ρ w1 v) = ρ w4 v := by
  apply difference_step h (rootElement 3 0) w1 w4
    [2, 1, 0, 1, 2] [2, 1, 0] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action2 : difference ρ (rootElement 2 0) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w0
    [1, 0, 1] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action3 : difference ρ (rootElement 2 0) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 2 0) w1
    [1, 0, 1] (by decide +kernel) 0 2 (by decide +kernel)
  decide +kernel

private theorem action4 : difference ρ (rootElement 2 0) (ρ w2 v) = ρ w4 v := by
  apply difference_step h (rootElement 2 0) w2 w4
    [2, 1, 0, 1, 2] [2, 1, 2, 0] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action5 : difference ρ (rootElement 1 0) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w0
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action6 : difference ρ (rootElement 1 0) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w1
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action7 : difference ρ (rootElement 1 0) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 1 0) w2
    [0] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action8 : difference ρ (rootElement 1 0) (ρ w3 v) = ρ w4 v := by
  apply difference_step h (rootElement 1 0) w3 w4
    [2, 1, 0, 1, 2] [2, 1, 0, 1, 2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private theorem action9 : difference ρ (rootElement 0 1) (ρ w0 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w0
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action10 : difference ρ (rootElement 0 1) (ρ w1 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w1
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action11 : difference ρ (rootElement 0 1) (ρ w2 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w2
    [] (by decide +kernel) 0 1 (by decide +kernel)
  decide +kernel

private theorem action12 : difference ρ (rootElement 0 1) (ρ w3 v) = 0 := by
  apply difference_zero h (rootElement 0 1) w3
    [] (by decide +kernel) 0 4 (by decide +kernel)
  decide +kernel

private theorem action13 : difference ρ (rootElement 0 1) (ρ w4 v) = ρ w3 v := by
  apply difference_step h (rootElement 0 1) w4 w3
    [2, 1, 0, 1, 2] [2, 1, 0, 1, 2] (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) <;> decide +kernel

private def vectors (ρ : Representation (ZMod 2) Group V) (v : V) : Fin 5 → V :=
  ![ρ w0 v, ρ w1 v, ρ w2 v, ρ w3 v, ρ w4 v]
private def extractors (ρ : Representation (ZMod 2) Group V) : Fin 5 → V →ₗ[ZMod 2] V :=
  ![LinearMap.id,
    (difference ρ (rootElement 3 0)).comp (LinearMap.id),
    (difference ρ (rootElement 2 0)).comp (LinearMap.id),
    (difference ρ (rootElement 1 0)).comp (LinearMap.id),
    (difference ρ (rootElement 0 1)).comp (LinearMap.id)]

private theorem independent (hv : v ≠ 0) : LinearIndependent (ZMod 2) (vectors ρ v) := by
  apply linearIndependent_of_triangular _ (extractors ρ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change difference ρ (rootElement 3 0) (ρ w0 v) = 0
      rw [action0 h]
    · change difference ρ (rootElement 2 0) (ρ w0 v) = 0
      rw [action2 h]
    · change difference ρ (rootElement 2 0) (ρ w1 v) = 0
      rw [action3 h]
    · change difference ρ (rootElement 1 0) (ρ w0 v) = 0
      rw [action5 h]
    · change difference ρ (rootElement 1 0) (ρ w1 v) = 0
      rw [action6 h]
    · change difference ρ (rootElement 1 0) (ρ w2 v) = 0
      rw [action7 h]
    · change difference ρ (rootElement 0 1) (ρ w0 v) = 0
      rw [action9 h]
    · change difference ρ (rootElement 0 1) (ρ w1 v) = 0
      rw [action10 h]
    · change difference ρ (rootElement 0 1) (ρ w2 v) = 0
      rw [action11 h]
    · change difference ρ (rootElement 0 1) (ρ w3 v) = 0
      rw [action12 h]
  · intro i
    fin_cases i
    · change ρ w0 v ≠ 0
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 3 0) (ρ w1 v) ≠ 0
      rw [action1 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 2 0) (ρ w2 v) ≠ 0
      rw [action4 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 1 0) (ρ w3 v) ≠ 0
      rw [action8 h]
      exact translate_ne_zero ρ _ hv
    · change difference ρ (rootElement 0 1) (ρ w4 v) ≠ 0
      rw [action13 h]
      exact translate_ne_zero ρ _ hv

theorem degree_le [Module.Finite (ZMod 2) V] (hv : v ≠ 0) :
    5 ≤ Module.finrank (ZMod 2) V := by
  simpa using (independent h hv).fintype_card_le_finrank
theorem finrank_eq [Module.Finite (ZMod 2) V] [IsIrreducible ρ]
    (hv : v ≠ 0) : Module.finrank (ZMod 2) V = 5 := by
  exact le_antisymm (h.finrank_le_five_of_endpoint hv (by decide +kernel)) (degree_le h hv)
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap.Case3
