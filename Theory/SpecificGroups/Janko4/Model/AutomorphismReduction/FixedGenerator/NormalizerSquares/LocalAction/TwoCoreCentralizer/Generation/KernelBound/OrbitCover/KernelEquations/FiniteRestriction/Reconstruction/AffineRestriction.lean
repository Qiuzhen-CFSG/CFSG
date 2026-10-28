module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.FlagChecks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.Equations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.KernelSpanning

/-!
# Affine restriction from invertibility and mixed-space preservation

The two mixed-space preservation conditions imply the 2373 checked linear
equations. Certified full Gaussian elimination places every solution in the
span of the affine directions and three scalar generators.

The checked flag conjugates every affine direction to a strictly upper
triangular matrix. Identity and two further matrices separate the three
scalar diagonal blocks. An invertible upper triangular binary matrix has
diagonal entries one; the three selected entries therefore force the scalar
part to be exactly identity.

The final theorem combines these certificates with the flag argument, using
only invertibility and the two mixed-space preservation conditions.
See Reconstruction/source/README.md for the exact original contract and
AffineRestriction/source/README.md for the certificate provenance.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
open LinearMembership
namespace AffineCertificate

theorem affineDirections_strict (X : RestrictionMatrix) (hX : X ∈ affineDirections) :
    ∀ i j : Fin 50, j ≤ i → flagConjugation X i j = 0 := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact affineDirection_strict k
  | zero =>
      intro i j _
      rw [map_zero]
      rfl
  | add x y _ _ hx hy =>
      intro i j hij
      rw [map_add, Matrix.add_apply, hx i j hij, hy i j hij, add_zero]
  | smul c x _ hx =>
      intro i j hij
      rw [map_smul, Matrix.smul_apply, hx i j hij, smul_zero]

theorem flagConjugation_isUnit (S : RestrictionMatrix) (hS : IsUnit S) :
    IsUnit (flagConjugation S) := by
  have hP : IsUnit flagMatrix :=
    ⟨⟨flagMatrix, flagInverse, flag_mul_flagInverse, flagInverse_mul_flag⟩, rfl⟩
  have hPi : IsUnit flagInverse :=
    ⟨⟨flagInverse, flagMatrix, flagInverse_mul_flag, flag_mul_flagInverse⟩, rfl⟩
  exact (hPi.mul hS).mul hP

theorem upper_unit_diagonal (S : RestrictionMatrix) (hS : IsUnit S)
    (hupper : S.IsUpperTriangular) (i : Fin 50) : S i i = 1 := by
  have hd : S.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero
  rw [Matrix.det_of_isUpperTriangular hupper] at hd
  have hi : S i i ≠ 0 := by
    intro hi
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  exact (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) (S i i) hi

theorem candidate_upper (X : RestrictionMatrix) (hX : X ∈ affineDirections)
    (a : Fin 3 → ZMod 2) :
    (flagConjugation (X + scalarLift a)).IsUpperTriangular := by
  intro i j hij
  have hne : i ≠ j := ne_of_gt hij
  change flagConjugation
    (X + (a 0 • (1 : RestrictionMatrix) +
      a 1 • scalarDirection 0 + a 2 • scalarDirection 1)) i j = 0
  simp only [map_add, map_smul, Matrix.add_apply, Matrix.smul_apply,
    flagConjugation_one, Matrix.one_apply, if_neg hne,
    affineDirections_strict X hX i j (le_of_lt hij),
    scalarDirection_upper 0 hij, scalarDirection_upper 1 hij,
    smul_zero, add_zero]

theorem candidate_diagonal (X : RestrictionMatrix) (hX : X ∈ affineDirections)
    (a : Fin 3 → ZMod 2) (i : Fin 50) :
    flagConjugation (X + scalarLift a) i i =
      a 0 + a 1 * (if i.val < 10 then 1 else 0) +
        a 2 * (if 10 ≤ i.val ∧ i.val < 40 then 1 else 0) := by
  simp [scalarLift, map_add, map_smul, flagConjugation_one,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    affineDirections_strict X hX i i le_rfl, scalarDirection_diagonal]

/-- The scalar diagonal obstruction is the only obstruction inside the candidate space. -/
theorem mem_affineDirections_of_isUnit_mem_candidateAlgebra
    (S : RestrictionMatrix) (hunit : IsUnit S) (hS : S ∈ candidateAlgebra) :
    S - 1 ∈ affineDirections := by
  obtain ⟨X, hX, Y, hY, hXY⟩ := Submodule.mem_sup.mp hS
  obtain ⟨a, rfl⟩ := hY
  subst S
  have hd := upper_unit_diagonal _ (flagConjugation_isUnit _ hunit)
    (candidate_upper X hX a)
  have h0 : a 0 = 1 := by
    simpa only [candidate_diagonal X hX a, show ¬(40 : Fin 50).val < 10 by decide,
      show ¬(10 ≤ (40 : Fin 50).val ∧ (40 : Fin 50).val < 40) by decide,
      if_false, mul_zero, add_zero] using hd 40
  have h1 : a 1 = 0 := by
    have hh := hd 0
    rw [candidate_diagonal X hX a] at hh
    simp only [show (0 : Fin 50).val < 10 by decide,
      show ¬(10 ≤ (0 : Fin 50).val ∧ (0 : Fin 50).val < 40) by decide,
      if_true, if_false, mul_one, mul_zero, add_zero, h0] at hh
    exact add_left_cancel (hh.trans (add_zero 1).symm)
  have h2 : a 2 = 0 := by
    have hh := hd 10
    rw [candidate_diagonal X hX a] at hh
    simp only [show ¬(10 : Fin 50).val < 10 by decide,
      show (10 ≤ (10 : Fin 50).val ∧ (10 : Fin 50).val < 40) by decide,
      and_self, if_true, if_false, mul_one, mul_zero, add_zero, h0] at hh
    exact add_left_cancel (hh.trans (add_zero 1).symm)
  have ha : scalarLift a = 1 := by
    simp [scalarLift, h0, h1, h2]
  simpa only [ha, add_sub_cancel_right] using hX

end AffineCertificate

/-- Assembly with an explicit mixed-space completeness certificate. -/
theorem mem_affineDirections_of_mixed_of_candidate_containment
    (hcomplete : ∀ S : RestrictionMatrix,
      PreservesMixedSpace S → PreservesMixedSpace (pairingAdjoint S) →
        S ∈ AffineCertificate.candidateAlgebra)
    (S : RestrictionMatrix) (hunit : IsUnit S)
    (hmixed : PreservesMixedSpace S)
    (hadjoint : PreservesMixedSpace (pairingAdjoint S)) :
    S - 1 ∈ affineDirections :=
  AffineCertificate.mem_affineDirections_of_isUnit_mem_candidateAlgebra
    S hunit (hcomplete S hmixed hadjoint)

/-- Assembly with explicit equation-source and kernel-spanning certificates. -/
theorem mem_affineDirections_of_mixed_of_equation_certificates
    (hsource : ∀ S : RestrictionMatrix,
      PreservesMixedSpace S → PreservesMixedSpace (pairingAdjoint S) →
        AffineCertificate.RawEquations S)
    (hkernel : ∀ S : RestrictionMatrix,
      AffineCertificate.RawEquations S → S ∈ AffineCertificate.candidateAlgebra)
    (S : RestrictionMatrix) (hunit : IsUnit S)
    (hmixed : PreservesMixedSpace S)
    (hadjoint : PreservesMixedSpace (pairingAdjoint S)) :
    S - 1 ∈ affineDirections :=
  AffineCertificate.mem_affineDirections_of_isUnit_mem_candidateAlgebra
    S hunit (hkernel S (hsource S hmixed hadjoint))

/-- Every invertible matrix preserving the mixed space together with its pairing
adjoint differs from identity by a combination of the published affine directions. -/
theorem mem_affineDirections_of_mixed
    (S : RestrictionMatrix) (hunit : IsUnit S)
    (hmixed : PreservesMixedSpace S)
    (hadjoint : PreservesMixedSpace (pairingAdjoint S)) :
    S - 1 ∈ affineDirections :=
  mem_affineDirections_of_mixed_of_equation_certificates
    AffineCertificate.rawEquations_of_mixed
    AffineCertificate.mem_candidateAlgebra_of_rawEquations
    S hunit hmixed hadjoint

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction
