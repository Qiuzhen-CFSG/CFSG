module
public import Theory.SpecificGroups.Held.CubicCentralizers.Initial
public import Theory.SpecificGroups.Held.CubicCentralizers.ListCount
public import Theory.SpecificGroups.Held.CubicCentralizers.ZeroChecks
import Mathlib.Tactic.FinCases
/-! Sparse graph cells bound the two native cubic centralizers by 1008
and 30240. Four fixed vertices determine a graph automorphism; the explicitly
counted invariant cells bound each successive orbit. Source: ATLAS HeG1-p2058B0,
Aschbacher–Smith 2.4.25, printed p.543. -/
public section
namespace Held.CubicCentralizers
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.OddCubeCandidates.CardinalityCertificates
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
set_option Elab.async false
set_option maxRecDepth 16384
theorem Xcell0_0_invariant : Invariant threeX 0 Xcell0_0 := by
  apply narrow_function threeX Xinitial0 (neighborCount Xsample0_0)
    (neighborCount_invariant threeX Xinitial0 Xsample0_0 1 Xsample0_0_spec) 0 83
  exact Xzero_check

theorem Xinvariant0 : Invariant threeX 0 Xcell0_0 := Xcell0_0_invariant
theorem Xcard0 : Nat.card {x : Fin 2058 // Xcell0_0 x.val = Xcell0_0 0} = 1008 := by
  rw [cell_card Xcell0_0 ⟨0,by decide⟩]
  decide +kernel

theorem Xcell1_0_invariant : Invariant threeX 1 Xcell1_0 := by
  apply narrow_function threeX Xinitial1 (neighborCount Xsample1_0)
    (neighborCount_invariant threeX Xinitial1 Xsample1_0 84 Xsample1_0_spec) 4 1
  have hn : Xsample1_0List.Nodup := by decide +kernel
  simp only [Xsample1_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xcell1_1_invariant : Invariant threeX 1 Xcell1_1 := by
  apply narrow_function threeX Xcell1_0_invariant (neighborCount Xsample1_1)
    (neighborCount_invariant threeX Xinitial1 Xsample1_1 85 Xsample1_1_spec) 1 3
  have hn : Xsample1_1List.Nodup := by decide +kernel
  simp only [Xsample1_1,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xcell1_2_invariant : Invariant threeX 1 Xcell1_2 := by
  apply narrow_function threeX Xcell1_1_invariant (neighborCount Xsample1_2)
    (neighborCount_invariant threeX Xinitial1 Xsample1_2 21 Xsample1_2_spec) 1 9
  have hn : Xsample1_2List.Nodup := by decide +kernel
  simp only [Xsample1_2,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xcell1_3_invariant : Invariant threeX 1 Xcell1_3 := by
  apply narrow_function threeX Xcell1_2_invariant (neighborCount Xsample1_3)
    (neighborCount_invariant threeX Xinitial1 Xsample1_3 81 Xsample1_3_spec) 1 1
  have hn : Xsample1_3List.Nodup := by decide +kernel
  simp only [Xsample1_3,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xinvariant1 : Invariant threeX 1 Xcell1_3 := Xcell1_3_invariant
theorem Xcard1 : Nat.card {x : Fin 2058 // Xcell1_3 x.val = Xcell1_3 1} = 1 := by
  rw [cell_card Xcell1_3 ⟨1,by decide⟩]
  decide +kernel

theorem Xcell2_0_invariant : Invariant threeX 2 Xcell2_0 := by
  apply narrow_function threeX Xinitial2 (neighborCount Xsample2_0)
    (neighborCount_invariant threeX Xinitial2 Xsample2_0 277 Xsample2_0_spec) 5 1
  have hn : Xsample2_0List.Nodup := by decide +kernel
  simp only [Xsample2_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xcell2_1_invariant : Invariant threeX 2 Xcell2_1 := by
  apply narrow_function threeX Xcell2_0_invariant (neighborCount Xsample2_1)
    (neighborCount_invariant threeX Xinitial2 Xsample2_1 5137 Xsample2_1_spec) 1 0
  have hn : Xsample2_1List.Nodup := by decide +kernel
  simp only [Xsample2_1,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xinvariant2 : Invariant threeX 2 Xcell2_1 := Xcell2_1_invariant
theorem Xcard2 : Nat.card {x : Fin 2058 // Xcell2_1 x.val = Xcell2_1 2} = 1 := by
  rw [cell_card Xcell2_1 ⟨2,by decide⟩]
  decide +kernel

theorem Xcell3_0_invariant : Invariant threeX 3 Xcell3_0 := by
  apply narrow_function threeX Xinitial3 (neighborCount Xsample3_0)
    (neighborCount_invariant threeX Xinitial3 Xsample3_0 332032 Xsample3_0_spec) 65 1
  have hn : Xsample3_0List.Nodup := by decide +kernel
  simp only [Xsample3_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xinvariant3 : Invariant threeX 3 Xcell3_0 := Xcell3_0_invariant
theorem Xcard3 : Nat.card {x : Fin 2058 // Xcell3_0 x.val = Xcell3_0 3} = 1 := by
  rw [cell_card Xcell3_0 ⟨3,by decide⟩]
  decide +kernel

theorem Zinvariant0 : Invariant threeZ 0 Zweight0 := Zinitial0
theorem Zcard0 : Nat.card {x : Fin 2058 // Zweight0 x.val = Zweight0 0} = 756 := by
  rw [cell_card Zweight0 ⟨0,by decide⟩]
  decide +kernel

theorem Zcell1_0_invariant : Invariant threeZ 1 Zcell1_0 := by
  apply narrow_function threeZ Zinitial1 (neighborCount Zsample1_0)
    (neighborCount_invariant threeZ Zinitial1 Zsample1_0 86 Zsample1_0_spec) 5 1
  have hn : Zsample1_0List.Nodup := by decide +kernel
  simp only [Zsample1_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zcell1_1_invariant : Invariant threeZ 1 Zcell1_1 := by
  apply narrow_function threeZ Zcell1_0_invariant (neighborCount Zsample1_1)
    (neighborCount_invariant threeZ Zinitial1 Zsample1_1 84 Zsample1_1_spec) 1 4
  have hn : Zsample1_1List.Nodup := by decide +kernel
  simp only [Zsample1_1,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zinvariant1 : Invariant threeZ 1 Zcell1_1 := Zcell1_1_invariant
theorem Zcard1 : Nat.card {x : Fin 2058 // Zcell1_1 x.val = Zcell1_1 1} = 40 := by
  rw [cell_card Zcell1_1 ⟨1,by decide⟩]
  decide +kernel

theorem Zcell2_0_invariant : Invariant threeZ 2 Zcell2_0 := by
  apply narrow_function threeZ Zinitial2 (neighborCount Zsample2_0)
    (neighborCount_invariant threeZ Zinitial2 Zsample2_0 5140 Zsample2_0_spec) 69 1
  have hn : Zsample2_0List.Nodup := by decide +kernel
  simp only [Zsample2_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zcell2_1_invariant : Invariant threeZ 2 Zcell2_1 := by
  apply narrow_function threeZ Zcell2_0_invariant (neighborCount Zsample2_1)
    (neighborCount_invariant threeZ Zinitial2 Zsample2_1 5381 Zsample2_1_spec) 1 0
  have hn : Zsample2_1List.Nodup := by decide +kernel
  simp only [Zsample2_1,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zinvariant2 : Invariant threeZ 2 Zcell2_1 := Zcell2_1_invariant
theorem Zcard2 : Nat.card {x : Fin 2058 // Zcell2_1 x.val = Zcell2_1 2} = 1 := by
  rw [cell_card Zcell2_1 ⟨2,by decide⟩]
  decide +kernel

theorem Zcell3_0_invariant : Invariant threeZ 3 Zcell3_0 := by
  apply narrow_function threeZ Zinitial3 (neighborCount Zsample3_0)
    (neighborCount_invariant threeZ Zinitial3 Zsample3_0 279573 Zsample3_0_spec) 320 1
  have hn : Zsample3_0List.Nodup := by decide +kernel
  simp only [Zsample3_0,neighborCount_list _ hn,adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zinvariant3 : Invariant threeZ 3 Zcell3_0 := Zcell3_0_invariant
theorem Zcard3 : Nat.card {x : Fin 2058 // Zcell3_0 x.val = Zcell3_0 3} = 1 := by
  rw [cell_card Zcell3_0 ⟨3,by decide⟩]
  decide +kernel

theorem graph_threeX_card_le : Nat.card (graphCentralizer threeX) ≤ 1008 := by
  apply card_le_of_cells threeX ![Xcell0_0,Xcell1_3,Xcell2_1,Xcell3_0] ![1008,1,1,1]
  · intro n; fin_cases n
    · exact Xinvariant0
    · exact Xinvariant1
    · exact Xinvariant2
    · exact Xinvariant3
  · intro n; fin_cases n
    · exact Xcard0.le
    · exact Xcard1.le
    · exact Xcard2.le
    · exact Xcard3.le

theorem graph_threeZ_card_le : Nat.card (graphCentralizer threeZ) ≤ 30240 := by
  apply card_le_of_cells threeZ ![Zweight0,Zcell1_1,Zcell2_1,Zcell3_0] ![756,40,1,1]
  · intro n; fin_cases n
    · exact Zinvariant0
    · exact Zinvariant1
    · exact Zinvariant2
    · exact Zinvariant3
  · intro n; fin_cases n
    · exact Zcard0.le
    · exact Zcard1.le
    · exact Zcard2.le
    · exact Zcard3.le
end Held.CubicCentralizers
