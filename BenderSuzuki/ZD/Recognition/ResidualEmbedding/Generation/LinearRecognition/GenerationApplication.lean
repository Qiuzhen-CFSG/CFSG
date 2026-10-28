module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Source

/-!
# Residual generation after proper-linear recognition

This extension applies the original generation assembly to the checked
proper-linear theorem. Only the genuine Section 15 linear-exclusion source
implication remains explicit.
The generation boundary is imported only by this consumer extension, never
by the recognition proof or its public boundary.

Source: GLS IV, Chapter 2, Theorem 12.1 and Propositions 14.1, 15.1.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Apply the original generation theorem with proper-linear recognition
proved; only the genuine Section 15 exclusion implication remains. -/
public theorem residualGeneration_of_linear_exclusion
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hnot : ¬ IsStronglyEmbedded M)
    (exclude : ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z, t ∉ M →
      residualGenerated M z t ≠ ⊤ → Even (Nat.card (residualPairStabilizer M t)) →
      ∀ n : ℕ, 2 ≤ n →
        (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) → False) :
    ResidualGeneration Z M := by
  exact residualGeneration_of_linear_analysis h.disconnected ha hnot
    (fun _ hz hzM _ ht htM hL heven =>
      proper_residualGenerated_linear h r ha hz hzM ht htM hL heven) exclude

end BenderSuzuki.ZD
