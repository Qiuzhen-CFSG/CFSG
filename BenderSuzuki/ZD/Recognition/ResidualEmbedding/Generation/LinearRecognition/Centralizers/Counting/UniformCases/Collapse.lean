module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Fusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Shearing
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion

/-!
# Centralizer collapse after the uniform alternatives

The local recognition data proves shearing, which supplies fusion of every
nondistinguished involution into the actual pair stabilizer. These discharge
the remaining earlier-source premises of the Section 13 unitary exclusion.
Applying it to the uniform alternatives leaves only the PSL₂ and Suzuki
cases, both of which give equality of `L` with each distinguished centralizer
closure. No counting-data record or centralizer-collapse premise is assumed.

The earlier Lemmas 12.3–12.4 local-recognition data remains explicit for the
enclosing centralizer assembly. All numerical, action, shearing, fusion, and
unitary-exclusion inputs used here have been discharged.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.7, 12.10–12.11 and
Proposition 13.1. The unitary argument uses the source subgroup-join normalizer.
-/

namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The uniform unitary branch is impossible using only the preceding local
recognition: shearing and nondistinguished fusion are constructed here. The
isomorphism is to the actual PSL₂ model with the distinguished field order. -/
public theorem proper_residualGenerated_unitary_centralizers_false_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n) : False := by
  have hshear := proper_residualGenerated_shearing_of_local
    h r ha hz hzM ht htM hL heven hlocal
  exact proper_residualGenerated_unitary_centralizers_false
    h r ha hz hzM ht htM hL heven hlocal hshear
    (proper_residualGenerated_nondistinguished_fusion_of_shearing
      h r ha hz hzM ht htM hL heven hshear)
    hn hcard e hunitary

/-- GLS4, Chapter 2, Proposition 13.1, conditional only on the earlier local
recognition: the distinguished centralizer closure of every involution in
the actual pair stabilizer equals the proper residual subgroup. The uniform
unitary branch, including either possible central cover, is excluded. -/
public theorem proper_residualGenerated_centralizerClosure_eq_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      centralizerClosure Z v = residualGenerated M z t := by
  obtain ⟨n, hn, hcard, hcases⟩ := proper_residualGenerated_uniform_cases_of_local
    h r ha hz hzM ht htM hL heven hlocal
  rcases hcases with ⟨_, _, hcollapse⟩ | ⟨m, _, _, _, _, hcollapse⟩ |
    ⟨⟨e⟩, hunitary, _, _⟩
  · intro v hvD hv
    exact (hcollapse v hvD hv).1
  · intro v hvD hv
    exact (hcollapse v hvD hv).1
  · exact (proper_residualGenerated_unitary_centralizers_false_of_local
      h r ha hz hzM ht htM hL heven hlocal hn hcard e hunitary).elim

end BenderSuzuki.ZD
