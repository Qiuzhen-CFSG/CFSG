module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Data120

/-!
# Checked rank-one expression, degree 120, phase 4

The packed data are untrusted candidates from `../source/density-120.json`
and `../source/density-252.json`. Each used identity is checked by the kernel. Membership of node 19, the
initial odd-order norm, remains an explicit hypothesis.
Source: ATLAS of Finite Group Representations, M24G1-f2r120B0 and f2r252B0;
James, J. Algebra 27 (1973), 57–111. The two matrices act on columns.
-/

set_option Elab.async false
@[expose] public section
open Matrix
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120

set_option maxRecDepth 8192 in
private theorem check20_factor : u20.map (combineList v20) = c19 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check20_action : v20.map (combineList c2) = w20 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check20_output : u20.map (combineList w20) = c20 := by decide +kernel

theorem mem20 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c20 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 10) c19 c2 c20 u20 v20 w20
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check20_factor check20_action check20_output
  rw [← h]
  exact Q.mul_mem hnorm (hA 1)

set_option maxRecDepth 8192 in
private theorem check21_factor : u21.map (combineList v21) = c20 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check21_action : v21.map (combineList c1) = w21 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check21_output : u21.map (combineList w21) = c21 := by decide +kernel

theorem mem21 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c21 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 10) c20 c1 c21 u21 v21 w21
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check21_factor check21_action check21_output
  rw [← h]
  exact Q.mul_mem (mem20 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check22_factor : u22.map (combineList v22) = c21 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check22_action : v22.map (combineList c19) = w22 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check22_output : u22.map (combineList w22) = c22 := by decide +kernel

theorem mem22 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c22 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 10) c21 c19 c22 u22 v22 w22
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check22_factor check22_action check22_output
  rw [← h]
  exact Q.mul_mem (mem21 Q hA hnorm) hnorm

set_option maxRecDepth 8192 in
private theorem check23_factor : u23.map (combineList v23) = c22 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check23_action : v23.map (combineList c1) = w23 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check23_output : u23.map (combineList w23) = c23 := by decide +kernel

theorem mem23 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c23 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 9) c22 c1 c23 u23 v23 w23
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check23_factor check23_action check23_output
  rw [← h]
  exact Q.mul_mem (mem22 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check24_factor : u24.map (combineList v24) = c23 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check24_action : v24.map (combineList c22) = w24 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check24_output : u24.map (combineList w24) = c24 := by decide +kernel

theorem mem24 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c24 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 9) c23 c22 c24 u24 v24 w24
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check24_factor check24_action check24_output
  rw [← h]
  exact Q.mul_mem (mem23 Q hA hnorm) (mem22 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem check25_factor : u25.map (combineList v25) = c24 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check25_action : v25.map (combineList c24) = w25 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check25_output : u25.map (combineList w25) = c25 := by decide +kernel

theorem mem25 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c25 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 8) c24 c24 c25 u25 v25 w25
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check25_factor check25_action check25_output
  rw [← h]
  exact Q.mul_mem (mem24 Q hA hnorm) (mem24 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem check26 : ∀ i : Fin 120, entry c25 i.val ^^^ entry c24 i.val = entry c26 i.val := by decide +kernel

theorem mem26 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c26 ∈ Q := by
  exact FactorAlgebras.Certificate.add_mem Q c25 c24 c26 (mem25 Q hA hnorm) (mem24 Q hA hnorm) check26

set_option maxRecDepth 8192 in
private theorem check27_factor : u27.map (combineList v27) = c26 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check27_action : v27.map (combineList c2) = w27 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check27_output : u27.map (combineList w27) = c27 := by decide +kernel

theorem mem27 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c27 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 7) c26 c2 c27 u27 v27 w27
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check27_factor check27_action check27_output
  rw [← h]
  exact Q.mul_mem (mem26 Q hA hnorm) (hA 1)


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120
