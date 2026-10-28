module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.ChecksSupport
import Mathlib.Tactic.FinCases

/-!
# Kernel checks for double-coset slice 1

Each row has the required pivot image and a key strictly smaller than the
next row. These checks certify 5760 distinct group elements in this slice.
Source: the retained ATLAS witnesses, encoded by `source/generate.py`.
-/

namespace Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
set_option maxRecDepth 100000
set_option Elab.async false

private theorem block_1_0 : ∀ i, RowValid 1 (blockRow 0 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_1 : ∀ i, RowValid 1 (blockRow 1 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_2 : ∀ i, RowValid 1 (blockRow 2 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_3 : ∀ i, RowValid 1 (blockRow 3 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_4 : ∀ i, RowValid 1 (blockRow 4 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_5 : ∀ i, RowValid 1 (blockRow 5 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_6 : ∀ i, RowValid 1 (blockRow 6 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_7 : ∀ i, RowValid 1 (blockRow 7 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_8 : ∀ i, RowValid 1 (blockRow 8 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_9 : ∀ i, RowValid 1 (blockRow 9 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_10 : ∀ i, RowValid 1 (blockRow 10 i) := by
  apply OrderCertificate.allFin
  decide +kernel

private theorem block_1_11 : ∀ i, RowValid 1 (blockRow 11 i) := by
  apply OrderCertificate.allFin
  decide +kernel

public theorem rows_valid_1 : ∀ i, RowValid 1 i := by
  apply allRows_of_blocks
  intro b
  fin_cases b
  · exact block_1_0
  · exact block_1_1
  · exact block_1_2
  · exact block_1_3
  · exact block_1_4
  · exact block_1_5
  · exact block_1_6
  · exact block_1_7
  · exact block_1_8
  · exact block_1_9
  · exact block_1_10
  · exact block_1_11

end Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
