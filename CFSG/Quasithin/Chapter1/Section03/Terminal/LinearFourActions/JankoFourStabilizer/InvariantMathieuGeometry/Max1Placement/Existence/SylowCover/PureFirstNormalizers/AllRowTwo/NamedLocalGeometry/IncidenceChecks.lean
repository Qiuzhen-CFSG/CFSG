module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.IncidenceData

/-!
# Kernel certificates for native row incidence

Each positive mask has an explicit seven-generator product preimage. Each
negative incidence has a row mask with a nonzero checked commutator against an
occurrence label. The negative checks are separated by row to bound memory;
`RowIncidence` applies both certificates to actual ambient subgroups.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and Proposition 2.2.3,
p.491; the native ATLAS coordinate conventions are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowIncidence
open FiniteConfigurations OccurrenceTable
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData.FiniteTree
attribute [local irreducible] modelGroup matrixA matrixB
attribute [local instance 2000] Finset.decidableDforallFinset
attribute [local instance 2000] Finset.decidableExistsAndFinset
set_option Elab.async false

theorem positive : ∀ i : Fin 26, ∀ j ∈ containing i, ∀ m ∈ rowMasks i,
    combo j (preimage j m) = m := by decide +kernel

private theorem excluded_0 : ∀ j : Fin 330, j ∉ containing 0 →
    (obstruction 0 j).1 ∈ rowMasks 0 ∧
    fastMultiply (obstruction 0 j).1.val (label j (obstruction 0 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 0 j).2).val (obstruction 0 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_1 : ∀ j : Fin 330, j ∉ containing 1 →
    (obstruction 1 j).1 ∈ rowMasks 1 ∧
    fastMultiply (obstruction 1 j).1.val (label j (obstruction 1 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 1 j).2).val (obstruction 1 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_2 : ∀ j : Fin 330, j ∉ containing 2 →
    (obstruction 2 j).1 ∈ rowMasks 2 ∧
    fastMultiply (obstruction 2 j).1.val (label j (obstruction 2 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 2 j).2).val (obstruction 2 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_3 : ∀ j : Fin 330, j ∉ containing 3 →
    (obstruction 3 j).1 ∈ rowMasks 3 ∧
    fastMultiply (obstruction 3 j).1.val (label j (obstruction 3 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 3 j).2).val (obstruction 3 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_4 : ∀ j : Fin 330, j ∉ containing 4 →
    (obstruction 4 j).1 ∈ rowMasks 4 ∧
    fastMultiply (obstruction 4 j).1.val (label j (obstruction 4 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 4 j).2).val (obstruction 4 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_5 : ∀ j : Fin 330, j ∉ containing 5 →
    (obstruction 5 j).1 ∈ rowMasks 5 ∧
    fastMultiply (obstruction 5 j).1.val (label j (obstruction 5 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 5 j).2).val (obstruction 5 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_6 : ∀ j : Fin 330, j ∉ containing 6 →
    (obstruction 6 j).1 ∈ rowMasks 6 ∧
    fastMultiply (obstruction 6 j).1.val (label j (obstruction 6 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 6 j).2).val (obstruction 6 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_7 : ∀ j : Fin 330, j ∉ containing 7 →
    (obstruction 7 j).1 ∈ rowMasks 7 ∧
    fastMultiply (obstruction 7 j).1.val (label j (obstruction 7 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 7 j).2).val (obstruction 7 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_8 : ∀ j : Fin 330, j ∉ containing 8 →
    (obstruction 8 j).1 ∈ rowMasks 8 ∧
    fastMultiply (obstruction 8 j).1.val (label j (obstruction 8 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 8 j).2).val (obstruction 8 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_9 : ∀ j : Fin 330, j ∉ containing 9 →
    (obstruction 9 j).1 ∈ rowMasks 9 ∧
    fastMultiply (obstruction 9 j).1.val (label j (obstruction 9 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 9 j).2).val (obstruction 9 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_10 : ∀ j : Fin 330, j ∉ containing 10 →
    (obstruction 10 j).1 ∈ rowMasks 10 ∧
    fastMultiply (obstruction 10 j).1.val (label j (obstruction 10 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 10 j).2).val (obstruction 10 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_11 : ∀ j : Fin 330, j ∉ containing 11 →
    (obstruction 11 j).1 ∈ rowMasks 11 ∧
    fastMultiply (obstruction 11 j).1.val (label j (obstruction 11 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 11 j).2).val (obstruction 11 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_12 : ∀ j : Fin 330, j ∉ containing 12 →
    (obstruction 12 j).1 ∈ rowMasks 12 ∧
    fastMultiply (obstruction 12 j).1.val (label j (obstruction 12 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 12 j).2).val (obstruction 12 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_13 : ∀ j : Fin 330, j ∉ containing 13 →
    (obstruction 13 j).1 ∈ rowMasks 13 ∧
    fastMultiply (obstruction 13 j).1.val (label j (obstruction 13 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 13 j).2).val (obstruction 13 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_14 : ∀ j : Fin 330, j ∉ containing 14 →
    (obstruction 14 j).1 ∈ rowMasks 14 ∧
    fastMultiply (obstruction 14 j).1.val (label j (obstruction 14 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 14 j).2).val (obstruction 14 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_15 : ∀ j : Fin 330, j ∉ containing 15 →
    (obstruction 15 j).1 ∈ rowMasks 15 ∧
    fastMultiply (obstruction 15 j).1.val (label j (obstruction 15 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 15 j).2).val (obstruction 15 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_16 : ∀ j : Fin 330, j ∉ containing 16 →
    (obstruction 16 j).1 ∈ rowMasks 16 ∧
    fastMultiply (obstruction 16 j).1.val (label j (obstruction 16 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 16 j).2).val (obstruction 16 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_17 : ∀ j : Fin 330, j ∉ containing 17 →
    (obstruction 17 j).1 ∈ rowMasks 17 ∧
    fastMultiply (obstruction 17 j).1.val (label j (obstruction 17 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 17 j).2).val (obstruction 17 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_18 : ∀ j : Fin 330, j ∉ containing 18 →
    (obstruction 18 j).1 ∈ rowMasks 18 ∧
    fastMultiply (obstruction 18 j).1.val (label j (obstruction 18 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 18 j).2).val (obstruction 18 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_19 : ∀ j : Fin 330, j ∉ containing 19 →
    (obstruction 19 j).1 ∈ rowMasks 19 ∧
    fastMultiply (obstruction 19 j).1.val (label j (obstruction 19 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 19 j).2).val (obstruction 19 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_20 : ∀ j : Fin 330, j ∉ containing 20 →
    (obstruction 20 j).1 ∈ rowMasks 20 ∧
    fastMultiply (obstruction 20 j).1.val (label j (obstruction 20 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 20 j).2).val (obstruction 20 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_21 : ∀ j : Fin 330, j ∉ containing 21 →
    (obstruction 21 j).1 ∈ rowMasks 21 ∧
    fastMultiply (obstruction 21 j).1.val (label j (obstruction 21 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 21 j).2).val (obstruction 21 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_22 : ∀ j : Fin 330, j ∉ containing 22 →
    (obstruction 22 j).1 ∈ rowMasks 22 ∧
    fastMultiply (obstruction 22 j).1.val (label j (obstruction 22 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 22 j).2).val (obstruction 22 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_23 : ∀ j : Fin 330, j ∉ containing 23 →
    (obstruction 23 j).1 ∈ rowMasks 23 ∧
    fastMultiply (obstruction 23 j).1.val (label j (obstruction 23 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 23 j).2).val (obstruction 23 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_24 : ∀ j : Fin 330, j ∉ containing 24 →
    (obstruction 24 j).1 ∈ rowMasks 24 ∧
    fastMultiply (obstruction 24 j).1.val (label j (obstruction 24 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 24 j).2).val (obstruction 24 j).1.val % 8192 := by
  decide +kernel

private theorem excluded_25 : ∀ j : Fin 330, j ∉ containing 25 →
    (obstruction 25 j).1 ∈ rowMasks 25 ∧
    fastMultiply (obstruction 25 j).1.val (label j (obstruction 25 j).2).val % 8192 ≠
      fastMultiply (label j (obstruction 25 j).2).val (obstruction 25 j).1.val % 8192 := by
  decide +kernel

theorem exclusions (i : Fin 26) : ∀ j : Fin 330, j ∉ containing i →
    (obstruction i j).1 ∈ rowMasks i ∧
    fastMultiply (obstruction i j).1.val (label j (obstruction i j).2).val % 8192 ≠
      fastMultiply (label j (obstruction i j).2).val (obstruction i j).1.val % 8192 := by
  fin_cases i
  · exact excluded_0
  · exact excluded_1
  · exact excluded_2
  · exact excluded_3
  · exact excluded_4
  · exact excluded_5
  · exact excluded_6
  · exact excluded_7
  · exact excluded_8
  · exact excluded_9
  · exact excluded_10
  · exact excluded_11
  · exact excluded_12
  · exact excluded_13
  · exact excluded_14
  · exact excluded_15
  · exact excluded_16
  · exact excluded_17
  · exact excluded_18
  · exact excluded_19
  · exact excluded_20
  · exact excluded_21
  · exact excluded_22
  · exact excluded_23
  · exact excluded_24
  · exact excluded_25


end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.RowIncidence
