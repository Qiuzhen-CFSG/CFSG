module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Stage5

/-!
# Checked rank-one expression, degree 120, phase 6

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
private theorem check36_factor : u36.map (combineList v36) = c35 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check36_action : v36.map (combineList c2) = w36 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check36_output : u36.map (combineList w36) = c36 := by decide +kernel

theorem mem36 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c36 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 5) c35 c2 c36 u36 v36 w36
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check36_factor check36_action check36_output
  rw [← h]
  exact Q.mul_mem (mem35 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check37_factor : u37.map (combineList v37) = c36 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check37_action : v37.map (combineList c1) = w37 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check37_output : u37.map (combineList w37) = c37 := by decide +kernel

theorem mem37 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c37 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 5) c36 c1 c37 u37 v37 w37
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check37_factor check37_action check37_output
  rw [← h]
  exact Q.mul_mem (mem36 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check38_factor : u38.map (combineList v38) = c37 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check38_action : v38.map (combineList c35) = w38 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check38_output : u38.map (combineList w38) = c38 := by decide +kernel

theorem mem38 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c38 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 5) c37 c35 c38 u38 v38 w38
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check38_factor check38_action check38_output
  rw [← h]
  exact Q.mul_mem (mem37 Q hA hnorm) (mem35 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem check39_factor : u39.map (combineList v39) = c38 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check39_action : v39.map (combineList c2) = w39 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check39_output : u39.map (combineList w39) = c39 := by decide +kernel

theorem mem39 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c39 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 4) c38 c2 c39 u39 v39 w39
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check39_factor check39_action check39_output
  rw [← h]
  exact Q.mul_mem (mem38 Q hA hnorm) (hA 1)

set_option maxRecDepth 8192 in
private theorem check40_factor : u40.map (combineList v40) = c39 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check40_action : v40.map (combineList c1) = w40 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check40_output : u40.map (combineList w40) = c40 := by decide +kernel

theorem mem40 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c40 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 4) c39 c1 c40 u40 v40 w40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check40_factor check40_action check40_output
  rw [← h]
  exact Q.mul_mem (mem39 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check41_factor : u41.map (combineList v41) = c40 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check41_action : v41.map (combineList c38) = w41 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check41_output : u41.map (combineList w41) = c41 := by decide +kernel

theorem mem41 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c41 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 4) c40 c38 c41 u41 v41 w41
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check41_factor check41_action check41_output
  rw [← h]
  exact Q.mul_mem (mem40 Q hA hnorm) (mem38 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem check42_factor : u42.map (combineList v42) = c41 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check42_action : v42.map (combineList c41) = w42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check42_output : u42.map (combineList w42) = c42 := by decide +kernel

theorem mem42 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c42 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 3) c41 c41 c42 u42 v42 w42
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check42_factor check42_action check42_output
  rw [← h]
  exact Q.mul_mem (mem41 Q hA hnorm) (mem41 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem check43_factor : u43.map (combineList v43) = c42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check43_action : v43.map (combineList c1) = w43 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check43_output : u43.map (combineList w43) = c43 := by decide +kernel

theorem mem43 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c43 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 2) c42 c1 c43 u43 v43 w43
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check43_factor check43_action check43_output
  rw [← h]
  exact Q.mul_mem (mem42 Q hA hnorm) (hA 0)

set_option maxRecDepth 8192 in
private theorem check44_factor : u44.map (combineList v44) = c43 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check44_action : v44.map (combineList c42) = w44 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem check44_output : u44.map (combineList w44) = c44 := by decide +kernel

theorem mem44 (Q : Subalgebra (ZMod 2) (Mat 120)) (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    matrix c44 ∈ Q := by
  have h := product_of_factor (n := 120) (r := 2) c43 c42 c44 u44 v44 w44
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    check44_factor check44_action check44_output
  rw [← h]
  exact Q.mul_mem (mem43 Q hA hnorm) (mem42 Q hA hnorm)

set_option maxRecDepth 8192 in
private theorem rankOne_checked : ∀ i : Fin 120, entry c44 i.val = if (entry colsList 0).testBit i.val then entry rowsOrbitList 0 else 0 := by decide +kernel

/-- The straight-line expression gives this literal rank-one operator. -/
theorem rankOne_mem (Q : Subalgebra (ZMod 2) (Mat 120))
    (hA : ∀ j, matrix120 j ∈ Q) (hnorm : matrix (n := 120) c19 ∈ Q) :
    vecMulVec (vector (entry colsList 0)) (vector (entry rowsOrbitList 0)) ∈ Q := by
  rw [← rankOne_eq c44 _ _ rankOne_checked]
  exact mem44 Q hA hnorm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120
