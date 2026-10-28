module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Frame.Certificates
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Geometry
public import Mathlib.Algebra.Field.ZMod

/-!
# Scalar rigidity of the concrete Rudvalis projective frame

The first 28 published line vectors are the columns of an explicitly checked
invertible matrix. Line 658 has nonzero coordinates in every basis direction.
An operator preserving the basis lines is diagonal in this basis, and its
eigenvector equation on line 658 forces all diagonal entries to coincide.
The eigenvalue on that line supplies the required unit-valued scalar.

The proof uses only the literal frame certificates, with no orbit-equivariance
or paired-group kernel hypothesis. `scalarKernel_of_orbitEquivariance` applies
it to the exact kernel consumer, leaving only the independent orbit certificate.

Source: ATLAS `2RuG1-f5r28B0`; this supplies the projective-frame ingredient
of the Rudvalis covering construction for Aschbacher–Smith I.1.3(1), printed
p.407. See `Frame/source/README.md` for the data and checking conventions.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section

private theorem rigidity_of_frame (v : Fin 4060 → Vec) (B C : Mat) (c : Vec)
    (hleft : C * B = 1) (hright : B * C = 1)
    (hbasis : ∀ j : Fin 28, (fun i => B i j) = v ⟨j.val, by omega⟩)
    (hdense : B.mulVec c = v 658)
    (hnonzero : ∀ j, c j ≠ 0) :
    ∀ M : Matˣ, (∀ i : Fin 4060, ∃ u : (ZMod 5)ˣ,
      (M : Mat).mulVec (v i) = (u : ZMod 5) • v i) →
      ∃ u : (ZMod 5)ˣ, M = Matrix.GeneralLinearGroup.scalar (Fin 28) u := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro M hM
  choose f hf using fun j : Fin 28 => hM ⟨j.val, by omega⟩
  obtain ⟨u, hu⟩ := hM 658
  let D : Mat := Matrix.diagonal (fun j => (f j : ZMod 5))
  have hMB : (M : Mat) * B = B * D := by
    ext i j
    have hj := congrFun (hf j) i
    rw [← hbasis j] at hj
    change (M : Mat).mulVec (fun k => B k j) i = (B * D) i j
    calc
      _ = (f j : ZMod 5) * B i j := hj
      _ = (B * D) i j := by rw [Matrix.mul_diagonal]; exact mul_comm _ _
  have hc : D.mulVec c = (u : ZMod 5) • c := by
    calc
      D.mulVec c = (C * (B * D)).mulVec c := by rw [← mul_assoc, hleft, one_mul]
      _ = C.mulVec ((M : Mat).mulVec (B.mulVec c)) := by
        rw [← hMB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
      _ = C.mulVec ((u : ZMod 5) • B.mulVec c) := by rw [hdense, hu]
      _ = (u : ZMod 5) • c := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hf_eq (j : Fin 28) : (f j : ZMod 5) = (u : ZMod 5) := by
    apply mul_right_cancel₀ (hnonzero j)
    simpa only [D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using congrFun hc j
  have hscalar : D = (u : ZMod 5) • (1 : Mat) := by
    rw [Matrix.smul_one_eq_diagonal]
    exact congrArg Matrix.diagonal (funext hf_eq)
  refine ⟨u, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]
  calc
    (M : Mat) = ((M : Mat) * B) * C := by rw [mul_assoc, hright, mul_one]
    _ = (B * D) * C := by rw [hMB]
    _ = (u : ZMod 5) • (1 : Mat) := by
      rw [hscalar, mul_smul_comm, mul_one, smul_mul_assoc, hright]

/-- Every invertible matrix preserving the published lines is a unit scalar. -/
theorem frameRigidity : FrameRigidity :=
  rigidity_of_frame lineVector Frame.basisMatrix Frame.inverseMatrix Frame.coordinates
    Frame.inverse_mul_basis Frame.basis_mul_inverse Frame.basis_column
    Frame.basis_mulVec_coordinates Frame.coordinates_ne_zero

/-- Discharge the frame premise in the literal paired-group kernel calculation. -/
theorem scalarKernel_of_orbitEquivariance (horbit : OrbitEquivariance) : ScalarKernel :=
  scalarKernel_of_geometry horbit frameRigidity

end
end Rudvalis.Multiplier.DoubleCover
