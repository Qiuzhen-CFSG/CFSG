module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Data

/-!
# Exhaustive symmetric coordinates for shears
The lexicographic list includes the diagonal, giving exactly 1275 independent
entries of a symmetric 50 by 50 matrix. Both inverse identities below are
checked in the kernel. Multiplication by the certified pairing inverse then
parameterizes every possible symplectic shear, and the retained last direction
is the identity matrix. No elimination assertion is made here.
Source: ../source/README.md and Shear/source/generate_data.py.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

attribute [local irreducible] pairingInverse restrictionPairing

private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem symmetricPositions_entry (i j : Fin 50) :
    symmetricPositions (symmetricEntry i j) = (min i j, max i j) := by
  revert i j
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem symmetricEntry_positions (k : Fin 1275) :
    symmetricEntry (symmetricPositions k).1 (symmetricPositions k).2 = k := by
  revert k
  decide +kernel

theorem symmetricMatrix_transpose (x : Parameter) :
    (symmetricMatrix x)ᵀ = symmetricMatrix x := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, symmetricMatrix, symmetricEntry,
    min_comm j i, max_comm j i]

theorem symmetricMatrix_parametersOf (M : RestrictionMatrix) (hM : Mᵀ = M) :
    symmetricMatrix (parametersOf M) = M := by
  apply Matrix.ext
  intro i j
  change M (symmetricPositions (symmetricEntry i j)).1
    (symmetricPositions (symmetricEntry i j)).2 = M i j
  rw [symmetricPositions_entry]
  by_cases hij : i ≤ j
  · simp only [min_eq_left hij, max_eq_right hij]
  · have hji : j ≤ i := le_of_not_ge hij
    simp only [min_eq_right hji, max_eq_left hji]
    exact congrArg (fun T : RestrictionMatrix => T i j) hM

theorem parametersOf_symmetricMatrix (x : Parameter) :
    parametersOf (symmetricMatrix x) = x := by
  funext k
  change x (symmetricEntry (symmetricPositions k).1
    (symmetricPositions k).2) = x k
  rw [symmetricEntry_positions]

/-- This covers every symmetric J C, including all fifty diagonal entries. -/
theorem shearOfParameter_parametersOf (C : RestrictionMatrix)
    (hC : (restrictionPairing * C)ᵀ = restrictionPairing * C) :
    shearOfParameter (parametersOf (restrictionPairing * C)) = C := by
  rw [shearOfParameter, symmetricMatrix_parametersOf _ hC, ← Matrix.mul_assoc,
    pairingInverse_mul_pairing, Matrix.one_mul]

theorem exists_parameter (C : RestrictionMatrix)
    (hC : (restrictionPairing * C)ᵀ = restrictionPairing * C) :
    ∃ x : Parameter, shearOfParameter x = C :=
  ⟨parametersOf (restrictionPairing * C), shearOfParameter_parametersOf C hC⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem symmetricMatrix_finalParameter :
    symmetricMatrix finalParameter = restrictionPairing := by
  decide +kernel

theorem shearOfParameter_finalParameter : shearOfParameter finalParameter = 1 := by
  rw [shearOfParameter, symmetricMatrix_finalParameter, pairingInverse_mul_pairing]

theorem shearOfParameter_zero : shearOfParameter 0 = 0 := by
  have h : symmetricMatrix 0 = 0 := rfl
  rw [shearOfParameter, h, Matrix.mul_zero]

theorem shearOfParameter_smul (a : ZMod 2) (x : Parameter) :
    shearOfParameter (a • x) = a • shearOfParameter x := by
  have h : symmetricMatrix (a • x) = a • symmetricMatrix x := rfl
  rw [shearOfParameter, h, Matrix.mul_smul, shearOfParameter]

theorem shearOfParameter_scalar_final (a : ZMod 2) :
    shearOfParameter (a • finalParameter) = 0 ∨
      shearOfParameter (a • finalParameter) = 1 := by
  have ha : a = 0 ∨ a = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
    exact h a
  rcases ha with rfl | rfl
  · left
    rw [zero_smul, shearOfParameter_zero]
  · right
    rw [one_smul, shearOfParameter_finalParameter]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear
