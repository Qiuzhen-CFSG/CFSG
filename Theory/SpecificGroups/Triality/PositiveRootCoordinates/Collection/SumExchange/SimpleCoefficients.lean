module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.Data
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Entries

/-!
# Binary coefficients of the pinned simple D₄ curves

The integral entry formulas on the full Geck lattice reduce to the concrete
binary coefficient tables. This checks both signs of each of the four simple
roots, including the quadratic and cubic terms; it supplies the starting point
for transport along arbitrary integral Tits words.

The finite comparisons are checked by Lean's kernel. The only reduction of
integral signs or Cartan entries occurs through the map from ℤ to `ZMod 2`.
Source: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), using the integral
entry formulas in `LeviRankOneMatrices.Entries`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction

namespace Triality.Standard.PositiveCoordinates.SumExchangeData

local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

def orderedIndex (i : Fin 4) : Index ≃ Index :=
  Equiv.sumCongr (Equiv.refl _) (rootOrder i)

theorem latticeEnumeration_orderedIndex (i : Fin 4) (r : Index) :
    latticeEnumeration (orderedIndex i r) = flatEquiv i r := by
  cases r <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem linearCoefficient_simple (i : Fin 4) (r s : Index) :
    linearCoefficient (simpleIndex i) (orderedIndex i r) (orderedIndex i s) =
      (eData i r s : ZMod 2) := by
  revert i r s
  simp only [Sum.forall]
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem linearCoefficient_negative_simple (i : Fin 4) (r s : Index) :
    linearCoefficient (negativeIndex (simpleIndex i)) (orderedIndex i r) (orderedIndex i s) =
      (fData i r s : ZMod 2) := by
  revert i r s
  simp only [Sum.forall]
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem quadraticCoefficient_simple (i : Fin 4) (r s : Index) :
    quadraticCoefficient (simpleIndex i) (orderedIndex i r) (orderedIndex i s) =
      if r = .inr 0 ∧ s = .inr 1 then 1 else 0 := by
  revert i r s
  simp only [Sum.forall]
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem quadraticCoefficient_negative_simple (i : Fin 4) (r s : Index) :
    quadraticCoefficient (negativeIndex (simpleIndex i)) (orderedIndex i r) (orderedIndex i s) =
      if r = .inr 1 ∧ s = .inr 0 then 1 else 0 := by
  revert i r s
  simp only [Sum.forall]
  decide +kernel

theorem eDividedPower_binary (i : Fin 4) (d : Fin 4) :
    Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm
      (specializeMatrix (eDividedPower (typeDRootPairing_baseEquiv 2 i) d)) =
      dividedCoefficient (simpleIndex i) d := by
  fin_cases d
  · simp [dividedCoefficient]
  all_goals
    ext r s
    obtain ⟨r, rfl⟩ := (orderedIndex i).surjective r
    obtain ⟨s, rfl⟩ := (orderedIndex i).surjective s
  · change (eDividedPower _ 1 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) =
      linearCoefficient (simpleIndex i) (orderedIndex i r) (orderedIndex i s)
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex,
      eDividedPower_one, eMatrix_entry]
    exact (linearCoefficient_simple i r s).symm
  · change (eDividedPower _ 2 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) =
      quadraticCoefficient (simpleIndex i) (orderedIndex i r) (orderedIndex i s)
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex, eTwo_entry,
      quadraticCoefficient_simple]
    split_ifs <;> norm_num
  · change (eDividedPower _ 3 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) = 0
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex, eThree_entry]
    rfl

theorem fDividedPower_binary (i : Fin 4) (d : Fin 4) :
    Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm
      (specializeMatrix (fDividedPower (typeDRootPairing_baseEquiv 2 i) d)) =
      dividedCoefficient (negativeIndex (simpleIndex i)) d := by
  fin_cases d
  · simp [dividedCoefficient]
  all_goals
    ext r s
    obtain ⟨r, rfl⟩ := (orderedIndex i).surjective r
    obtain ⟨s, rfl⟩ := (orderedIndex i).surjective s
  · change (fDividedPower _ 1 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) =
      linearCoefficient (negativeIndex (simpleIndex i)) (orderedIndex i r) (orderedIndex i s)
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex,
      fDividedPower_one, fMatrix_entry]
    exact (linearCoefficient_negative_simple i r s).symm
  · change (fDividedPower _ 2 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) =
      quadraticCoefficient (negativeIndex (simpleIndex i)) (orderedIndex i r) (orderedIndex i s)
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex, fTwo_entry,
      quadraticCoefficient_negative_simple]
    split_ifs <;> norm_num
  · change (fDividedPower _ 3 (latticeEnumeration (orderedIndex i r))
      (latticeEnumeration (orderedIndex i s)) : ZMod 2) = 0
    rw [latticeEnumeration_orderedIndex, latticeEnumeration_orderedIndex, fThree_entry]
    rfl

theorem positiveIndex_simplePosition (i : Fin 4) :
    positiveIndex (simplePosition i) = simpleIndex i := by
  fin_cases i <;> rfl

theorem canonicalCoefficient_simple (i : Fin 4) (d : Fin 4) :
    canonicalCoefficient (simplePosition i) d =
      dividedCoefficient (positiveIndex (simplePosition i)) d := by
  unfold canonicalCoefficient
  rw [rootIndex_simple, ← typeDRootPairing_baseEquiv_val]
  rw [rootDividedPower_of_pos _
    ((typeDRootPairing_base 2).isPos_of_mem_support (typeDRootPairing_baseEquiv 2 i).property)]
  simp only [rootRoute_word_simple, rootRoute_simple, transportedMatrix_nil,
    positiveIndex_simplePosition]
  exact eDividedPower_binary i d

theorem canonicalCoefficient_zero (i : Fin 12) :
    canonicalCoefficient i 0 = dividedCoefficient (positiveIndex i) 0 := by
  simp [canonicalCoefficient, dividedCoefficient]

theorem canonicalCoefficient_three (i : Fin 12) :
    canonicalCoefficient i 3 = dividedCoefficient (positiveIndex i) 3 := by
  unfold canonicalCoefficient
  rw [rootDividedPower_of_pos _ (rootIndex_positive i), specializeMatrix_transportedMatrix]
  obtain ⟨j, hj⟩ := (typeDRootPairing_baseEquiv 2).surjective
    (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple
  have he : specializeMatrix (S := ZMod 2)
      (eDividedPower (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple 3) = 0 := by
    apply (Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm).injective
    rw [← hj]
    simpa [dividedCoefficient] using eDividedPower_binary j 3
  change Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm
    (specializeMatrix (titsWord (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).word) *
      specializeMatrix (eDividedPower (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).simple 3) *
      specializeMatrix (titsWordInv (rootRoute (b := typeDRootPairing_base 2) (rootIndex i)).word)) = _
  rw [he]
  simp [dividedCoefficient]

end Triality.Standard.PositiveCoordinates.SumExchangeData
