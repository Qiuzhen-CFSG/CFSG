module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.WordEvaluation.Data
/-!
# Coordinate recurrence for the local seed conjugates

Each certified coordinate matrix is the identity plus a row update. On the
constant and free coordinates this increments one parameter; on a quadratic
coordinate it adds the sum of the other variables in terms containing that
parameter. A finite kernel check identifies these rows with actionRows and
checks that every quadratic term has distinct indices. The remaining proof is
linearity and the expansion of a square-free quadratic form at x + eᵢ.

This proves the recurrence for all binary parameters without enumerating masks.
The chart and word provenance is recorded in OrbitCover/source/README.md;
WordEvaluation/source/generate.py supplies the untrusted row witnesses.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.WordEvaluation
open OrbitCoverCoordinates
open scoped Matrix
set_option maxRecDepth 10000

private def derivative (i : Fin 12) (k : Fin 9) (x : Fin 12 → ZMod 2) : ZMod 2 :=
  ((quadraticTerms.get k).map fun p =>
    (if p.1 = i then x p.2 else 0) + (if p.2 = i then x p.1 else 0)).sum

private def derivativeRow (i : Fin 12) (k : Fin 9) : Fin 22 → ZMod 2 :=
  ((quadraticTerms.get k).map fun p =>
    (if p.1 = i then Pi.single (freeIndex p.2) 1 else 0) +
      (if p.2 = i then Pi.single (freeIndex p.1) 1 else 0)).sum

private def updateRow (i : Fin 12) (j : Fin 22) : Fin 22 → ZMod 2 :=
  if j.val = 0 then 0
  else if h : j.val < 13 then
    if j = freeIndex i then Pi.single 0 1 else 0
  else derivativeRow i ⟨j.val - 13, by omega⟩

set_option maxHeartbeats 3000000 in
private lemma coefficient_entries : ∀ (i : Fin 12) (j k : Fin 22),
    coefficientAction i j k = ((Pi.single j (1 : ZMod 2) : Fin 22 → ZMod 2) + updateRow i j) k := by
  change ∀ (i : Fin 12) (j k : Fin 22),
    (if ((actionRows.get i).get j).testBit k.val then (1 : ZMod 2) else 0) =
      ((Pi.single j (1 : ZMod 2) : Fin 22 → ZMod 2) + updateRow i j) k
  decide +kernel

private lemma terms_distinct : ∀ (k : Fin 9) (p : Fin 12 × Fin 12),
    p ∈ quadraticTerms.get k → p.1 ≠ p.2 := by
  decide +kernel

private lemma pair_update (i a b : Fin 12) (hab : a ≠ b) (x : Fin 12 → ZMod 2) :
    (x + Pi.single i 1 : Fin 12 → ZMod 2) a * (x + Pi.single i 1 : Fin 12 → ZMod 2) b =
      x a * x b + ((if a = i then x b else 0) + (if b = i then x a else 0)) := by
  by_cases ha : a = i <;> by_cases hb : b = i
  · exact False.elim (hab (ha.trans hb.symm))
  · simp [Pi.add_apply, ha, hb, add_mul]
  · simp [Pi.add_apply, ha, hb, mul_add]
  · simp [Pi.add_apply, ha, hb]

private lemma quadratic_update (i : Fin 12) (k : Fin 9) (x : Fin 12 → ZMod 2) :
    quadraticCoordinate k (x + Pi.single i 1) =
      quadraticCoordinate k x + derivative i k x := by
  unfold quadraticCoordinate derivative
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  exact pair_update i p.1 p.2 (terms_distinct k p hp) x

private lemma list_sum_dot (l : List (Fin 22 → ZMod 2)) (y : Fin 22 → ZMod 2) :
    l.sum ⬝ᵥ y = (l.map fun r => r ⬝ᵥ y).sum := by
  induction l with
  | nil => simp
  | cons r l ih => simp [add_dotProduct, ih]

private lemma derivativeRow_dot (i : Fin 12) (k : Fin 9) (x : Fin 12 → ZMod 2) :
    derivativeRow i k ⬝ᵥ parameterCoordinates x = derivative i k x := by
  unfold derivativeRow derivative
  rw [list_sum_dot, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases h1 : p.1 = i <;> by_cases h2 : p.2 = i <;>
    simp [h1, h2, add_dotProduct,
      parameterCoordinates_free]

private lemma coefficient_apply (i : Fin 12) (j : Fin 22) (y : Fin 22 → ZMod 2) :
    (coefficientAction i *ᵥ y) j = y j + updateRow i j ⬝ᵥ y := by
  change coefficientAction i j ⬝ᵥ y = _
  have he : coefficientAction i j = (Pi.single j 1 : Fin 22 → ZMod 2) + updateRow i j :=
    funext (coefficient_entries i j)
  rw [he, add_dotProduct, single_one_dotProduct]

private lemma updateRow_free (i t : Fin 12) :
    updateRow i (freeIndex t) =
      if t = i then (Pi.single 0 1 : Fin 22 → ZMod 2) else 0 := by
  have he : freeIndex t = freeIndex i ↔ t = i := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [freeIndex] at hv
      omega
    · exact congrArg freeIndex
  simp only [updateRow, show (freeIndex t).val ≠ 0 by dsimp [freeIndex]; omega,
    show (freeIndex t).val < 13 by dsimp [freeIndex]; omega,
    ↓reduceIte, ↓reduceDIte, he]

private lemma updateRow_quadratic (i : Fin 12) (k : Fin 9) :
    updateRow i (quadraticIndex k) = derivativeRow i k := by
  simp only [updateRow, quadraticIndex,
    show ¬ k.val + 13 = 0 by omega, show ¬ k.val + 13 < 13 by omega,
    ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel]

theorem coefficientAction_parameters (i : Fin 12) (x : Fin 12 → ZMod 2) :
    coefficientAction i *ᵥ parameterCoordinates x =
      parameterCoordinates (x + Pi.single i 1) := by
  funext j
  by_cases h0 : j.val = 0
  · have hj : j = 0 := Fin.ext h0
    subst j
    rw [coefficient_apply]
    simp [updateRow, parameterCoordinates_zero]
  · by_cases h1 : j.val < 13
    · let t : Fin 12 := ⟨j.val - 1, by omega⟩
      have hj : j = freeIndex t := Fin.ext (by dsimp [freeIndex, t]; omega)
      rw [hj, coefficient_apply, updateRow_free, parameterCoordinates_free,
        parameterCoordinates_free]
      by_cases ht : t = i <;>
        simp [ht, Pi.add_apply, parameterCoordinates_zero]
    · let k : Fin 9 := ⟨j.val - 13, by omega⟩
      have hj : j = quadraticIndex k := Fin.ext (by dsimp [quadraticIndex, k]; omega)
      rw [hj, coefficient_apply, updateRow_quadratic, parameterCoordinates_quadratic,
        parameterCoordinates_quadratic, derivativeRow_dot, quadratic_update]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.WordEvaluation
