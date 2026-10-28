module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Source

/-!
# The proper residual subgroup is linear

The full Lemma 12.2 alternatives identify the actual proper residual subgroup
as a binary PSL₂ group or a Suzuki group. In the Suzuki case, the proved
centralizer collapse and marked coset counts instantiate the source exclusion.
Thus the original subgroup itself has a PSL₂(2^n) model with n ≥ 2. No local
geometry, counting, centralizer or model-recognition premise remains.

Source: GLS IV, Chapter 2, Lemma 12.2 and Proposition 14.1. The separate
Section 15 exclusion remains the next input to residual generation.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The actual proper residual subgroup is PSL₂(2^n), n ≥ 2, with every
centralizer, counting and Suzuki-exclusion input discharged. -/
public theorem proper_residualGenerated_linear
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) := by
  obtain ⟨n, hn, hmodels⟩ :=
    proper_residualGenerated_models h r ha hz hzM ht htM hL heven
  rcases hmodels with hlinear | ⟨m, hm, _, ⟨e⟩⟩
  · exact ⟨n, hn, hlinear⟩
  · obtain ⟨hdegree, hfixed⟩ :=
      proper_residualGenerated_suzuki_counts h r ha hz hzM ht htM hL heven hm e
    exact (proper_residualGenerated_suzuki_false h r ha hz hzM ht htM hL heven m hm e
      (proper_residualGenerated_centralizerClosure h r ha hz hzM ht htM hL heven)
      hdegree hfixed).elim

end BenderSuzuki.ZD
