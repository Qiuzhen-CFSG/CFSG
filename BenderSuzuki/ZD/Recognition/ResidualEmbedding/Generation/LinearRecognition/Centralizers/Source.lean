module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion

/-!
# Centralizer collapse in the proper residual case

The proved local data supply shearing, fusion and the three uniform counting
alternatives. The first two alternatives already identify each distinguished
centralizer closure with the original residual subgroup. The third is the
unitary configuration excluded by the independent Section 13 argument.
The Suzuki numerical specialization uses the original marked Suzuki model.

Source: GLS IV, Chapter 2, Proposition 13.1 and Lemma 12.10.
-/

namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Proposition 13.1, with the local, shearing, counting and unitary inputs
all discharged from the original proper-residual hypotheses. -/
public theorem proper_residualGenerated_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t := by
  have hlocal := proper_residualGenerated_centralizer_local_data
    h r ha hz hzM ht htM hL heven
  have hcount := proper_residualGenerated_centralizer_counting_of_local
    h r ha hz hzM ht htM hL heven hlocal
  obtain ⟨n, hn, hcard, hcases⟩ := hcount.cases
  rcases hcases with ⟨_, _, hc⟩ | ⟨_, _, _, _, _, hc⟩ | ⟨⟨e⟩, hu, _, _⟩
  · exact fun u hu hv => (hc u hu hv).1
  · exact fun u hu hv => (hc u hu hv).1
  · exact (proper_residualGenerated_unitary_centralizers_false
      h r ha hz hzM ht htM hL heven hlocal hcount.shearing
      hcount.nondistinguished_fusion hn hcard e hu).elim

/-- Lemma 12.10 in the actual Suzuki model, retaining its field exponent and
the literal ambient coset and fixed-coset counts. -/
public theorem proper_residualGenerated_suzuki_counts
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    {m : ℕ} (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m) :
    let q := 2 ^ (2 * m + 1)
    Nat.card (G ⧸ M) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) ∧
      ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
        Nat.card {beta : G ⧸ M // u • beta = beta} = q ^ 2 + 1 :=
  proper_residualGenerated_suzuki_counts_of_local h r ha hz hzM ht htM hL heven
    (proper_residualGenerated_centralizer_local_data h r ha hz hzM ht htM hL heven) hm e

end BenderSuzuki.ZD
