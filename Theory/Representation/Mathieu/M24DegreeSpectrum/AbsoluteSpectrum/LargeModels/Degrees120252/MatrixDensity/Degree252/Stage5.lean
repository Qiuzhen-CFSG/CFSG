module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Stage4

/-!
# Checked rank-one expression, degree 252, phase 5

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
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252

set_option maxRecDepth 8192 in
private theorem check28_factor : u28.map (combineList v28) = c27 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check28_action : v28.map (combineList c2) = w28 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check28_output : u28.map (combineList w28) = c28 := by decide +kernel

theorem mem28 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c28 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c27 c2 c28 u28 v28 w28
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check28_factor check28_action check28_output
  rw [← h]
  exact Q.mul_mem (mem27 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check29_factor : u29.map (combineList v29) = c28 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check29_action : v29.map (combineList c1) = w29 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check29_output : u29.map (combineList w29) = c29 := by decide +kernel

theorem mem29 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c29 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c28 c1 c29 u29 v29 w29
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check29_factor check29_action check29_output
  rw [← h]
  exact Q.mul_mem (mem28 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check30_factor : u30.map (combineList v30) = c29 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check30_action : v30.map (combineList c2) = w30 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check30_output : u30.map (combineList w30) = c30 := by decide +kernel

theorem mem30 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c30 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c29 c2 c30 u30 v30 w30
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check30_factor check30_action check30_output
  rw [← h]
  exact Q.mul_mem (mem29 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check31_factor : u31.map (combineList v31) = c30 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check31_action : v31.map (combineList c1) = w31 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check31_output : u31.map (combineList w31) = c31 := by decide +kernel

theorem mem31 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c31 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c30 c1 c31 u31 v31 w31
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check31_factor check31_action check31_output
  rw [← h]
  exact Q.mul_mem (mem30 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check32_factor : u32.map (combineList v32) = c31 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check32_action : v32.map (combineList c2) = w32 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check32_output : u32.map (combineList w32) = c32 := by decide +kernel

theorem mem32 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c32 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c31 c2 c32 u32 v32 w32
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check32_factor check32_action check32_output
  rw [← h]
  exact Q.mul_mem (mem31 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check33_factor : u33.map (combineList v33) = c32 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check33_action : v33.map (combineList c1) = w33 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check33_output : u33.map (combineList w33) = c33 := by decide +kernel

theorem mem33 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c33 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c32 c1 c33 u33 v33 w33
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check33_factor check33_action check33_output
  rw [← h]
  exact Q.mul_mem (mem32 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check34_factor : u34.map (combineList v34) = c33 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check34_action : v34.map (combineList c2) = w34 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check34_output : u34.map (combineList w34) = c34 := by decide +kernel

theorem mem34 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c34 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c33 c2 c34 u34 v34 w34
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check34_factor check34_action check34_output
  rw [← h]
  exact Q.mul_mem (mem33 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check35_factor : u35.map (combineList v35) = c34 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check35_action : v35.map (combineList c1) = w35 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check35_output : u35.map (combineList w35) = c35 := by decide +kernel

theorem mem35 (Q : Subalgebra (ZMod 2) (Mat 252)) (hA : ∀ j, matrix252 j ∈ Q) (hnorm : matrix (n := 252) c19 ∈ Q) :
    matrix c35 ∈ Q := by
  have h := product_of_factor (n := 252) (r := 2) c34 c1 c35 u35 v35 w35
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check35_factor check35_action check35_output
  rw [← h]
  exact Q.mul_mem (mem34 Q hA hnorm) (hA 0)


end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252
