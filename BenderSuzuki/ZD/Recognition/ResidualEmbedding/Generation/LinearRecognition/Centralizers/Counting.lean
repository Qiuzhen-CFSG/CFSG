module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Suzuki
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Shearing
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Fusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Collapse

/-!
# Counting in the proper residual centralizer analysis

`proper_residualGenerated_centralizer_counting_of_local` assembles shearing,
centralization, nondistinguished fusion, and the three uniform alternatives.
Only the local-recognition conclusions of Lemmas 12.3–12.4 remain explicit;
the earlier action congruence and Thompson counts are proved prerequisites.
`proper_residualGenerated_suzuki_counts_of_local` then specializes the degree
and fixed-coset counts to the field parameter of a supplied Suzuki isomorphism.

`Counting.Suzuki` proves centralization and centralizer-closure collapse for
an actual Suzuki model from local recognition, and recovers its field
parameter when specializing the general counting data.

`Counting.Shearing` proves that all involutions of the pair stabilizer shear,
from the proper residual structure and the explicit local-recognition data.
It also supplies fusion of commuting mixed products for the following counts.

`Counting.UniformCases.Source` constructs the Lemma 12.8 numerical data and
the earlier action congruence and orbit bound, excludes the noncentral field
action, and proves Lemma 12.9 and the uniform model and degree alternatives.

`Counting.UniformCases.Collapse` constructs shearing and nondistinguished
fusion from local recognition, excludes the unitary branch by Section 13,
and proves centralizer-closure equality. Only the earlier local-recognition
data remains explicit for the enclosing counting and centralizer assemblies.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.5–12.11 and Proposition 13.1.
-/

namespace BenderSuzuki.ZD
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The shearing, centralization, uniform counting and fusion conclusions of
GLS4, Chapter 2, Lemmas 12.7–12.11, conditional only on the preceding local
recognition. The uniform alternatives retain the unitary branch for the
independent Section 13 argument. -/
public theorem proper_residualGenerated_centralizer_counting_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ResidualCentralizerCountingData Z M z t := by
  have hshear := proper_residualGenerated_shearing_of_local
    h r ha hz hzM ht htM hL heven hlocal
  exact {
    shearing := hshear
    centralizes := proper_residualGenerated_centralizes_of_local
      h r ha hz hzM ht htM hL heven hlocal
    nondistinguished_fusion := proper_residualGenerated_nondistinguished_fusion_of_shearing
      h r ha hz hzM ht htM hL heven hshear
    cases := proper_residualGenerated_uniform_cases_of_local
      h r ha hz hzM ht htM hL heven hlocal }

/-- The ambient degree and all pair-involution fixed-coset counts in the
actual Suzuki model. The Borel marking identifies the model's field order
with the distinguished subgroup order; no counting or parameter-matching
premise is required beyond the preceding local recognition. -/
public theorem proper_residualGenerated_suzuki_counts_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m) :
    let q := 2 ^ (2 * m + 1)
    Nat.card (G ⧸ M) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) ∧
      ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
        Nat.card {beta : G ⧸ M // v • beta = beta} = q ^ 2 + 1 :=
  ResidualCentralizerCountingData.suzuki_counts h r ha hz hzM ht htM hL heven
    (proper_residualGenerated_centralizer_counting_of_local
      h r ha hz hzM ht htM hL heven hlocal) hm e

end BenderSuzuki.ZD
