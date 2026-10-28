module
public import Theory.SpecificGroups.Held.CubicCentralizers.Data
public import Theory.SpecificGroups.Held.CubicCentralizers.ListCount
import Mathlib.Tactic.FinCases
/-! Kernel checks for the only large sample cell in the Held cubic
centralizer bound. The proved list evaluator traverses each sample once;
128-point blocks bound the cost of individual declarations. -/
public section
namespace Held.CubicCentralizers
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.OddCubeCandidates.CardinalityCertificates
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
set_option Elab.async false
set_option maxRecDepth 16384
private theorem zero0 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(0*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero1 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(1*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero2 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(2*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero3 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(3*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero4 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(4*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero5 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(5*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero6 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(6*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero7 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(7*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero8 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(8*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero9 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(9*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero10 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(10*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero11 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(11*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero12 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(12*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero13 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(13*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero14 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(14*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero15 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(15*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

private theorem zero16 : ∀ r : Fin 128,
    let v : Fin 2058 := ⟨(16*128+r.val)%2058,Nat.mod_lt _ (by decide)⟩
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧
      Xsample0_0List.countP (fun y => (fastRow v).testBit y.val) = 83 then 1 else 0 := by
  apply allFin
  decide +kernel

theorem Xzero_check : ∀ v : Fin 2058,
    Xcell0_0 v.val = if Xweight0 v.val = 0 ∧ neighborCount Xsample0_0 v = 83 then 1 else 0 := by
  have hn : Xsample0_0List.Nodup := by decide +kernel
  simp only [Xsample0_0,neighborCount_list _ hn,adj_iff_fast,Bool.decide_eq_true]
  apply allPoints
  intro q
  fin_cases q
  · exact zero0
  · exact zero1
  · exact zero2
  · exact zero3
  · exact zero4
  · exact zero5
  · exact zero6
  · exact zero7
  · exact zero8
  · exact zero9
  · exact zero10
  · exact zero11
  · exact zero12
  · exact zero13
  · exact zero14
  · exact zero15
  · exact zero16
end Held.CubicCentralizers
