module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.Basic

/-!
# Assembly boundary for the residual generation theorem

Theorem 12.1 of GLS, Volume 4, Chapter 2 follows by assuming the generated
subgroup `L` is proper. Sections 12–14 then identify `L` with `L₂(2^n)`,
where `n ≥ 2`; Section 15 rules out that actual model. The theorem below
assembles these two still-explicit obligations, deriving the even order of
`D` from double transitivity and failure of strong embedding.

The model witness is a multiplicative equivalence with the concrete binary
projective special linear group. Neither this conditional assembly nor the
preliminary lemmas assert the missing analyses of Sections 12–15.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Theorem 12.1 and Propositions 14.1, 15.1.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory

universe u

/-- Conditional assembly of the proper-subgroup linear identification and
its exclusion. The unconditional `residualGeneration_of_action` still needs
both source arguments; the action premise is permitted by the parent task. -/
public theorem residualGeneration_of_linear_analysis
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hnot : ¬ IsStronglyEmbedded M)
    (linear : ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z, t ∉ M →
      residualGenerated M z t ≠ ⊤ → Even (Nat.card (residualPairStabilizer M t)) →
      ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n))
    (exclude : ∀ z ∈ Z, z ∈ M → ∀ t ∈ Z, t ∉ M →
      residualGenerated M z t ≠ ⊤ → Even (Nat.card (residualPairStabilizer M t)) →
      ∀ n : ℕ, 2 ≤ n →
        (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) → False) :
    ResidualGeneration Z M := by
  intro z hz hzM t ht htM
  by_contra hL
  have heven := residualPairStabilizer_even h ha.two_transitive hnot htM
  obtain ⟨n, hn, ⟨e⟩⟩ := linear z hz hzM t ht htM hL heven
  exact exclude z hz hzM t ht htM hL heven n hn e

end BenderSuzuki.ZD
