module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.AmbientObstruction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Inputs
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Blocks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.RadicalK
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear

/-!
# The full homology-kernel vector stabilizer

The actual stabilizer consists of the two distinct elements 1 and the
central involution. The certified displacement calculation forces S = 1;
the radical-K upper bound and mixed tests force D = B = 0; the two shear
tests leave C = 0 or 1. The full adapted-basis equality test then determines
the original 112-dimensional matrix as 1 or A.

The unconditional group theorem supplies every finite premise using the
actual generated matrix group's invariant bilinear form and exterior span.
The original ambient counterexample is retained: commutation with A, trivial
homology action and fixation of (A - 1)e₀ require these genuine restrictions.

Source motivation: GLS3, Table 5.3i, printed p.270. Its centralizer structure
is not assumed. See VectorStabilizer/source/README.md for the exact finite
contracts and the unchanged column-action conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound

/-- The certified involution is a second element of the actual stabilizer. -/
theorem kernelInvolution_ne_one : kernelInvolution ≠ 1 := by
  intro h
  have he : centralInvolution = 1 :=
    congrArg (fun c : homologyAction.ker => (c : involutionCentralizer)) h
  have ho := orderOf_centralInvolution
  rw [he, orderOf_one] at ho
  contradiction

/-- The actual stabilizer contains the two distinct elements 1 and a. -/
theorem two_le_card_vectorStabilizer : 2 ≤ Nat.card vectorStabilizer := by
  let z : vectorStabilizer := ⟨kernelInvolution, kernelInvolution_mem_vectorStabilizer⟩
  have hz : z ≠ 1 := by
    intro h
    exact kernelInvolution_ne_one
      (congrArg (fun c : vectorStabilizer => (c : homologyAction.ker)) h)
  have hpos : 0 < Nat.card vectorStabilizer := Nat.card_pos
  have hne : Nat.card vectorStabilizer ≠ 1 := by
    intro he
    have hs := (Nat.card_eq_one_iff_unique.mp he).1
    exact hz (hs.elim z 1)
  omega

/-- Assemble the full stabilizer conclusion from independent finite
certificates. The unconditional theorem below supplies all four. -/
theorem vector_stabilizer_eq_one_or_involution_of_certificates
    (hrad : VectorStabilizer.RadicalKUpperBound)
    (hdisplacement : ∀ g : BinaryMatrixˣ,
      OrbitCoverCoordinates.KernelConditions g →
      OrbitCoverCoordinates.formPullback g OrbitCoverCoordinates.invariantForm =
        OrbitCoverCoordinates.invariantForm →
      g ∈ OrbitCoverCoordinates.formStabilizer OrbitCoverCoordinates.exteriorFormSpace →
      (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector →
      OrbitCoverCoordinates.restrictionMatrix g = 1)
    (hoffDiagonal : VectorStabilizer.RadicalKUpperBound → ∀ g : BinaryMatrixˣ,
      OrbitCoverCoordinates.KernelConditions g →
      OrbitCoverCoordinates.formPullback g OrbitCoverCoordinates.invariantForm =
        OrbitCoverCoordinates.invariantForm →
      g ∈ OrbitCoverCoordinates.formStabilizer OrbitCoverCoordinates.exteriorFormSpace →
      OrbitCoverCoordinates.restrictionMatrix g = 1 →
      VectorStabilizer.middleRightBlock g = 0 ∧ VectorStabilizer.upperMiddleBlock g = 0)
    (hshear : VectorStabilizer.RadicalKUpperBound → ∀ g : BinaryMatrixˣ,
      OrbitCoverCoordinates.KernelConditions g →
      OrbitCoverCoordinates.formPullback g OrbitCoverCoordinates.invariantForm =
        OrbitCoverCoordinates.invariantForm →
      g ∈ OrbitCoverCoordinates.formStabilizer OrbitCoverCoordinates.exteriorFormSpace →
      OrbitCoverCoordinates.restrictionMatrix g = 1 →
      VectorStabilizer.middleRightBlock g = 0 → VectorStabilizer.upperMiddleBlock g = 0 →
      VectorStabilizer.upperRightBlock g = 0 ∨ VectorStabilizer.upperRightBlock g = 1)
    (c : homologyAction.ker)
    (hc : naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) = baseVector) :
    (c : involutionCentralizer) = 1 ∨ (c : involutionCentralizer) = centralInvolution := by
  apply VectorStabilizer.vector_stabilizer_of_finite_implication ?_ c hc
  intro g hk hf he hx
  have hS := hdisplacement g hk hf he hx
  obtain ⟨hD, hB⟩ := hoffDiagonal hrad g hk hf he hS
  exact VectorStabilizer.eq_one_or_matrixUnitA_of_blocks g hk hS hB hD
    (hshear hrad g hk hf he hS hD hB)

namespace VectorStabilizer
open OrbitCoverCoordinates

/-- The complete finite matrix implication: every block in the adapted
112-dimensional basis is determined by the four stated conditions. -/
theorem eq_one_or_matrixUnitA_of_fixed_base (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hfix : (g : BinaryMatrix) *ᵥ (baseVector : NaturalModule) = baseVector) :
    g = 1 ∨ g = matrixUnitA := by
  have hS := restriction_eq_one_of_fixed_base g hker hform hext hfix
  obtain ⟨hD, hB⟩ := offDiagonal_eq_zero radicalK_upper g hker hform hext hS
  exact eq_one_or_matrixUnitA_of_blocks g hker hS hB hD
    (shear_eq_zero_or_one radicalK_upper g hker hform hext hS hD hB)

end VectorStabilizer

/-- Every element of the full homology kernel fixing the marked vector is
the identity or the central involution. All finite certificates are discharged. -/
theorem vector_stabilizer_eq_one_or_involution (c : homologyAction.ker)
    (hc : naturalAction (c : involutionCentralizer) (baseVector : NaturalModule) = baseVector) :
    (c : involutionCentralizer) = 1 ∨ (c : involutionCentralizer) = centralInvolution :=
  VectorStabilizer.vector_stabilizer_of_finite_implication
    VectorStabilizer.eq_one_or_matrixUnitA_of_fixed_base c hc

/-- The full homology-kernel point stabilizer has exactly two elements. -/
theorem vectorStabilizer_card_eq_two : Nat.card vectorStabilizer = 2 :=
  Nat.le_antisymm
    (vectorStabilizer_card_le_of_fixers vector_stabilizer_eq_one_or_involution)
    two_le_card_vectorStabilizer

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound
