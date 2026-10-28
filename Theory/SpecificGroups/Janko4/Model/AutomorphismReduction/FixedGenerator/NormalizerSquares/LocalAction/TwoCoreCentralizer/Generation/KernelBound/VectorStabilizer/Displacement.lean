module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Inputs
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.FixedSpace
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Nilpotence
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.SelfAdjoint
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Separation

/-!
# The marked restriction's displacement

The certified fixed-column and eigenvector kernels put S - 1 in the
102-generator square-zero space. Thus S is an involution, and preservation
of J makes S - 1 self-adjoint. The complete self-adjoint coefficient kernel
puts it in the 45-generator space, where preservation of the actual
restricted exterior forms forces it to vanish.

The final theorem discharges both finite certificates and uses exactly the
kernel, form-preservation and marked-vector hypotheses. It concludes identity
of the restriction; the full 112-dimensional stabilizer assembly is separate.
The precise finite argument and matrix provenance are recorded in
VectorStabilizer/source/README.md and Displacement/source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
namespace Displacement

attribute [local irreducible] restrictionMatrix restrictionPairing nilSpace selfAdjointSpace

theorem square_eq_one_of_nil {S : RestrictionMatrix} (h : S - 1 ∈ nilSpace) :
    S * S = 1 := by
  have hs : S = 1 + (S - 1) := by abel
  have hx := nilSpace_square h
  have htwo : (S - 1) + (S - 1) = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero ((S - 1) i j)
  calc
    S * S = (1 + (S - 1)) * (1 + (S - 1)) := congrArg₂ (· * ·) hs hs
    _ = 1 := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hx, add_zero]
      rw [add_assoc, htwo, add_zero]

theorem displacement_selfAdjoint {S : RestrictionMatrix} (hnil : S - 1 ∈ nilSpace)
    (hpair : Sᵀ * restrictionPairing * S = restrictionPairing) :
    (S - 1)ᵀ * restrictionPairing = restrictionPairing * (S - 1) := by
  have h := congrArg (fun M => M * S) hpair
  rw [Matrix.mul_assoc, square_eq_one_of_nil hnil, Matrix.mul_one] at h
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_one, h]

end Displacement
open Displacement

/-- Conditional assembly of the two independent finite certificates.
Neither certificate is part of the original marked-restriction hypothesis. -/
theorem restriction_eq_one_of_fixed_base_of_displacement_certificates
    (hcut : ∀ X : RestrictionMatrix, X ∈ nilSpace →
      Xᵀ * restrictionPairing = restrictionPairing * X → X ∈ selfAdjointSpace)
    (hseparate : ∀ X : RestrictionMatrix, X ∈ selfAdjointSpace →
      (∀ R : RestrictionMatrix, R ∈ restrictionExteriorSpace →
        (1 + X)ᵀ * R * (1 + X) ∈ restrictionExteriorSpace) → X = 0)
    (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    restrictionMatrix g = 1 := by
  have hnil := displacement_mem_nil (restrictionMatrix_inverse_mul g hker)
    (restriction_mem_of_fixed_base g hker hform hext hfix)
    (restriction_fixes_first g hker hfix)
  have hself := hcut _ hnil
    (displacement_selfAdjoint hnil (restrictionMatrix_pairing g hker hform))
  have hzero := hseparate _ hself (fun R hR => by
    have hS : 1 + (restrictionMatrix g - 1) = restrictionMatrix g := by abel
    rw [hS]
    exact restriction_preserves_exterior g hker hext hR)
  exact sub_eq_zero.mp hzero

/-- A kernel element preserving the invariant form and exterior span and fixing
the marked vector acts identically on the displacement coordinates. -/
theorem restriction_eq_one_of_fixed_base
    (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    restrictionMatrix g = 1 :=
  restriction_eq_one_of_fixed_base_of_displacement_certificates
    selfAdjoint_mem selfAdjoint_rigidity g hker hform hext hfix

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
