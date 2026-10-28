module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.Contracts
@[expose] public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
/-!
# Checked upper row segments

Each numerical check extracts the upper segment of an ordered tensor row and
XORs it with the strict upper segment of the reversed row. The diagonal is
retained exactly once. Natural-number traversals avoid nested finite-index
recursors; their coverage is proved before the checks are assembled.
Source conventions: ../source/README.md and ../../../../source/README.md.
-/

set_option Elab.async false

def checkRow (p s t a : ℕ) : Bool :=
  ((p >>> (1+125*a-a*(a-1)/2)) % 2^(125-a)) ==
    (((s >>> (125*a+a)) ^^^ ((t >>> (125*a+a+1)) <<< 1)) % 2^(125-a))

theorem checkRow_spec (p s t : ℕ) (a : Fin 125) :
    checkRow p s t a.val = true ↔ RowCheck p s t a := by
  simp only [checkRow, beq_iff_eq, RowCheck, slot, Nat.sub_self, Nat.add_zero, Nat.mul_comm]

def checkPolar (e : ℕ) : Bool :=
  if h : e < 987 then
    let i : Fin 987 := ⟨e,h⟩
    (List.range 125).all (checkRow (equationRows.get i) (ordered.get i) (reversed.get i))
  else false

theorem checkPolar_spec (e : Fin 987) (h : checkPolar e.val = true) : PolarizationCheck e := by
  intro a
  simp only [checkPolar, dif_pos e.isLt] at h
  exact (checkRow_spec _ _ _ a).mp
    (List.all_eq_true.mp h a.val (List.mem_range.mpr a.isLt))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check000 : (List.range' 0 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check050 : (List.range' 50 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check100 : (List.range' 100 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check150 : (List.range' 150 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check200 : (List.range' 200 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check250 : (List.range' 250 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check300 : (List.range' 300 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check350 : (List.range' 350 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check400 : (List.range' 400 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check450 : (List.range' 450 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check500 : (List.range' 500 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check550 : (List.range' 550 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check600 : (List.range' 600 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check650 : (List.range' 650 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check700 : (List.range' 700 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check750 : (List.range' 750 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check800 : (List.range' 800 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check850 : (List.range' 850 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check900 : (List.range' 900 50).all checkPolar = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem check950 : (List.range' 950 37).all checkPolar = true := by
  decide +kernel

public theorem polarizations_checked : ∀ e : Fin 987, PolarizationCheck e := by
  intro e
  apply checkPolar_spec e
  by_cases h0 : e.val < 50
  · exact List.all_eq_true.mp check000 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h50 : e.val < 100
  · exact List.all_eq_true.mp check050 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h100 : e.val < 150
  · exact List.all_eq_true.mp check100 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h150 : e.val < 200
  · exact List.all_eq_true.mp check150 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h200 : e.val < 250
  · exact List.all_eq_true.mp check200 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h250 : e.val < 300
  · exact List.all_eq_true.mp check250 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h300 : e.val < 350
  · exact List.all_eq_true.mp check300 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h350 : e.val < 400
  · exact List.all_eq_true.mp check350 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h400 : e.val < 450
  · exact List.all_eq_true.mp check400 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h450 : e.val < 500
  · exact List.all_eq_true.mp check450 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h500 : e.val < 550
  · exact List.all_eq_true.mp check500 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h550 : e.val < 600
  · exact List.all_eq_true.mp check550 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h600 : e.val < 650
  · exact List.all_eq_true.mp check600 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h650 : e.val < 700
  · exact List.all_eq_true.mp check650 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h700 : e.val < 750
  · exact List.all_eq_true.mp check700 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h750 : e.val < 800
  · exact List.all_eq_true.mp check750 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h800 : e.val < 850
  · exact List.all_eq_true.mp check800 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h850 : e.val < 900
  · exact List.all_eq_true.mp check850 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h900 : e.val < 950
  · exact List.all_eq_true.mp check900 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  exact List.all_eq_true.mp check950 e.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
