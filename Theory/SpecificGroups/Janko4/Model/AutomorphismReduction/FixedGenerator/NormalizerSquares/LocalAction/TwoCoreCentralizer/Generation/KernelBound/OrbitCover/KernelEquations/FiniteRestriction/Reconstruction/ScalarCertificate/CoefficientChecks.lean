module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.FirstJ
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.FirstE
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.SecondJ
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.SecondE

/-! Closed binary arithmetic for the scalar certificate. The direction products
are checked in four blocks to limit kernel memory. The resulting row products,
Gram matrix, and linear coefficients are interpreted in Directions.
Source and witness conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

theorem weight_check : ∀ k : Fin 124,
    secondFactorsJ.get k ^^^ secondFactorsE.get k = directionWeights.get k := by decide +kernel


theorem identity_j_check : ∀ i : Fin 50,
    rowProduct (jRows.get i) fjRows = identityWeightJRows.get i := by decide +kernel

theorem identity_e_check : ∀ i : Fin 50,
    rowProduct (eRows.get i) feRows = identityWeightERows.get i := by decide +kernel

theorem identity_weight_check : ∀ i j : Fin 50,
    bit (identityWeightJRows.get i) j.val + bit (identityWeightERows.get i) j.val =
      bit identityWeightBits (50 * i.val + j.val) := by decide +kernel


theorem identity_check : ∀ i j : Fin 50,
    bit identityBits (50 * i.val + j.val) = if i = j then (1 : ZMod 2) else 0 := by
  decide +kernel


theorem weight_bound : ∀ k : Fin 124, directionWeights.get k < 2 ^ 2500 := by
  decide +kernel


theorem identity_weight_bound : identityWeightBits < 2 ^ 2500 := by decide +kernel


theorem gram_check : ∀ i j : Fin 124,
    bit (foldParity 12 (directionWeights.get i &&& affineDirectionRows.get j)) 0 =
      bit (gramRows.get i) j.val := by decide +kernel


theorem gram_symmetric : ∀ i j : Fin 124,
    bit (gramRows.get i) j.val = bit (gramRows.get j) i.val := by decide +kernel


theorem linear_check : ∀ k : Fin 124,
    bit (gramRows.get k) k.val +
      bit (foldParity 12 (identityWeightBits &&& affineDirectionRows.get k)) 0 +
      bit (foldParity 12 (directionWeights.get k &&& identityBits)) 0 =
      bit 17552799707978362774193210816690218843 k.val := by decide +kernel


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
