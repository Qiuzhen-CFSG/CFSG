module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction

/-!
# Source inputs for the proper Suzuki exclusion

This packages only the hypotheses of the Suzuki branch of GLS4, Chapter 2,
Proposition 14.1. The three centralizer and permutation premises are the outputs
of Sections 12–13; their producer is independent of this branch. In particular
neither regularity, centralizer embedding, Sylow structure nor fusion is an
input here. The concrete Suzuki parameter is `q = 2^(2*m+1)`.

The final exclusion must construct all subsequent local geometry from these
inputs. This record is an interface for those proofs, not the proposition.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open PFAppendixIII

universe u

/-- The literal source inputs, with an actual equivalence to the matrix group. -/
public structure Context {G : Type u} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) (z t : G) (m : ℕ) where
  minimal : MinimalCounterexample Z M
  reduction : SimpleReduction Z M
  action : ResidualAction Z M
  z_mem : z ∈ Z
  z_mem_M : z ∈ M
  t_mem : t ∈ Z
  t_not_mem_M : t ∉ M
  proper : residualGenerated M z t ≠ ⊤
  even_pair : Even (Nat.card (residualPairStabilizer M t))
  parameter_pos : 1 ≤ m
  model : residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m
  centralizers : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
    centralizerClosure Z u = residualGenerated M z t
  degree : Nat.card (G ⧸ M) =
    ((2 ^ (2 * m + 1)) ^ 2 + 1) *
      ((2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) + 1)
  fixed : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
    Nat.card {beta : G ⧸ M // u • beta = beta} = (2 ^ (2 * m + 1)) ^ 2 + 1

end BenderSuzuki.ZD.SuzukiExclusion
