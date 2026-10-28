module

public import Theory.Comparator.Defs
public import BenderSuzuki.Converse.PSU3

/-!
# Identifying the shared binary PSU₃ carrier

The determinant-one isometries in `PSU3Model f` are exactly the special
subgroup of the standard antidiagonal Hermitian form. Thus its closure adds
no elements, and the two projective models are equal inside the same PGL.
The matrix field remains `GaloisField 2 (2*f)` throughout.

Source: the standard unitary construction of Huppert II.10.12, with the
explicit field and form supplied by `BenderSuzuki.Converse.PSU3`.
-/

public section
namespace BenderSuzuki.MatrixGroups
open Subgroup BenderSuzuki.Converse

/-- Equality of the actual subgroups of PGL, without a field change. -/
theorem psu3Model_eq_projective (f : ℕ) [NeZero f] :
    PSU3Model f = ProjectiveSpecialUnitaryMatrixGroup (uform f) := by
  unfold PSU3Model ProjectiveSpecialUnitaryMatrixGroup
  congr 1
  have he : {A : GL (Fin 3) (GaloisField 2 (2 * f)) |
      (Matrix.of fun i j =>
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) j i ^ (2 ^ f)) *
        !![0,0,1;0,1,0;1,0,0] * (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) = !![0,0,1;0,1,0;1,0,0] ∧
      Matrix.GeneralLinearGroup.det A = 1} = ((uform f).specialSubgroup : Set _) := by
    ext A
    have hct : (uform f).conjTranspose A = Matrix.of (fun i j =>
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) j i ^ (2 ^ f)) := by
      ext i j
      exact uconj_apply f (A.val j i)
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, HermitianForm.mem_specialSubgroup_iff,
      hct, uform_form]
  rw [he, closure_eq]

end BenderSuzuki.MatrixGroups
