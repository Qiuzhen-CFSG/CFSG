module
public import Theory.SpecificGroups.Held.CubicCentralizers.Data
import Mathlib.Tactic.FinCases
/-! Kernel-checked initial signatures and completeness of the sparse sample
cells for the Held cubic-centralizer bounds. Source: ATLAS HeG1-p2058B0. -/
public section
namespace Held.CubicCentralizers
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.OddCubeCandidates.CardinalityCertificates
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
set_option Elab.async false
set_option maxRecDepth 16384
theorem Xinitial0 : Invariant threeX 0 Xweight0 := by
  apply initial_labels_invariant threeX 0 [] (by simp) Xweight0
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xsample0_0_spec : ∀ x : Fin 2058, x ∈ Xsample0_0 ↔ Xweight0 x.val = 1 := by
  apply sample_spec_of_count Xweight0 1 Xsample0_0
  · have hall : Xsample0_0List.all (fun x => decide (Xweight0 x.val = 1)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xinitial1 : Invariant threeX 1 Xweight1 := by
  apply initial_labels_invariant threeX 1 [0] (by simp) Xweight1
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xsample1_0_spec : ∀ x : Fin 2058, x ∈ Xsample1_0 ↔ Xweight1 x.val = 84 := by
  apply sample_spec_of_count Xweight1 84 Xsample1_0
  · have hall : Xsample1_0List.all (fun x => decide (Xweight1 x.val = 84)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xsample1_1_spec : ∀ x : Fin 2058, x ∈ Xsample1_1 ↔ Xweight1 x.val = 85 := by
  apply sample_spec_of_count Xweight1 85 Xsample1_1
  · have hall : Xsample1_1List.all (fun x => decide (Xweight1 x.val = 85)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xsample1_2_spec : ∀ x : Fin 2058, x ∈ Xsample1_2 ↔ Xweight1 x.val = 21 := by
  apply sample_spec_of_count Xweight1 21 Xsample1_2
  · have hall : Xsample1_2List.all (fun x => decide (Xweight1 x.val = 21)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xsample1_3_spec : ∀ x : Fin 2058, x ∈ Xsample1_3 ↔ Xweight1 x.val = 81 := by
  apply sample_spec_of_count Xweight1 81 Xsample1_3
  · have hall : Xsample1_3List.all (fun x => decide (Xweight1 x.val = 81)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xinitial2 : Invariant threeX 2 Xweight2 := by
  apply initial_labels_invariant threeX 2 [0, 1] (by simp) Xweight2
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xsample2_0_spec : ∀ x : Fin 2058, x ∈ Xsample2_0 ↔ Xweight2 x.val = 277 := by
  apply sample_spec_of_count Xweight2 277 Xsample2_0
  · have hall : Xsample2_0List.all (fun x => decide (Xweight2 x.val = 277)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xsample2_1_spec : ∀ x : Fin 2058, x ∈ Xsample2_1 ↔ Xweight2 x.val = 5137 := by
  apply sample_spec_of_count Xweight2 5137 Xsample2_1
  · have hall : Xsample2_1List.all (fun x => decide (Xweight2 x.val = 5137)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Xinitial3 : Invariant threeX 3 Xweight3 := by
  apply initial_labels_invariant threeX 3 [0, 1, 2] (by simp) Xweight3
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Xsample3_0_spec : ∀ x : Fin 2058, x ∈ Xsample3_0 ↔ Xweight3 x.val = 332032 := by
  apply sample_spec_of_count Xweight3 332032 Xsample3_0
  · have hall : Xsample3_0List.all (fun x => decide (Xweight3 x.val = 332032)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Zinitial0 : Invariant threeZ 0 Zweight0 := by
  apply initial_labels_invariant threeZ 0 [] (by simp) Zweight0
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zinitial1 : Invariant threeZ 1 Zweight1 := by
  apply initial_labels_invariant threeZ 1 [0] (by simp) Zweight1
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zsample1_0_spec : ∀ x : Fin 2058, x ∈ Zsample1_0 ↔ Zweight1 x.val = 86 := by
  apply sample_spec_of_count Zweight1 86 Zsample1_0
  · have hall : Zsample1_0List.all (fun x => decide (Zweight1 x.val = 86)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Zsample1_1_spec : ∀ x : Fin 2058, x ∈ Zsample1_1 ↔ Zweight1 x.val = 84 := by
  apply sample_spec_of_count Zweight1 84 Zsample1_1
  · have hall : Zsample1_1List.all (fun x => decide (Zweight1 x.val = 84)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Zinitial2 : Invariant threeZ 2 Zweight2 := by
  apply initial_labels_invariant threeZ 2 [0, 1] (by simp) Zweight2
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zsample2_0_spec : ∀ x : Fin 2058, x ∈ Zsample2_0 ↔ Zweight2 x.val = 5140 := by
  apply sample_spec_of_count Zweight2 5140 Zsample2_0
  · have hall : Zsample2_0List.all (fun x => decide (Zweight2 x.val = 5140)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Zsample2_1_spec : ∀ x : Fin 2058, x ∈ Zsample2_1 ↔ Zweight2 x.val = 5381 := by
  apply sample_spec_of_count Zweight2 5381 Zsample2_1
  · have hall : Zsample2_1List.all (fun x => decide (Zweight2 x.val = 5381)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

theorem Zinitial3 : Invariant threeZ 3 Zweight3 := by
  apply initial_labels_invariant threeZ 3 [0, 1, 2] (by simp) Zweight3
  simp only [initial, adj_iff_fast]
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem Zsample3_0_spec : ∀ x : Fin 2058, x ∈ Zsample3_0 ↔ Zweight3 x.val = 279573 := by
  apply sample_spec_of_count Zweight3 279573 Zsample3_0
  · have hall : Zsample3_0List.all (fun x => decide (Zweight3 x.val = 279573)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx))
  · decide +kernel

end Held.CubicCentralizers
