module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry

/-!
# Exclusion of the proper Suzuki model

The regular moved-coset action embeds the actual centralizer in the specified
Suzuki group. This constructs the local geometry and discharges every input
of the Sylow/fusion contradiction. The only extra premises are the original
Sections 12–13 centralizer-closure and coset-count outputs; proper-linear
recognition supplies these from their checked source theorems.

The model uses q = 2^(2*m+1), m ≥ 1, and keeps the original ambient group,
pair stabilizer, distinguished set and actual multiplicative equivalence.
Source: GLS IV, Chapter 2, Proposition 14.1.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Exclude the actual Suzuki model using precisely the centralizer and
coset-count outputs supplied by Sections 12–13. -/
public theorem proper_residualGenerated_suzuki_false
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (m : ℕ) (hm : 1 ≤ m)
    (e : residualGenerated M z t ≃* MatrixGroups.SuzukiMatrixGroup m)
    (hcentralizers : ∀ v ∈ residualPairStabilizer M t,
      PFAppendixIII.IsInvolution v → centralizerClosure Z v = residualGenerated M z t)
    (hdegree : Nat.card (G ⧸ M) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        ((2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) + 1))
    (hfixed : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      Nat.card {beta : G ⧸ M // v • beta = beta} = (2 ^ (2 * m + 1)) ^ 2 + 1) :
    False := by
  let d : SuzukiExclusion.Context Z M z t m := {
    minimal := h
    reduction := r
    action := ha
    z_mem := hz
    z_mem_M := hzM
    t_mem := ht
    t_not_mem_M := htM
    proper := hL
    even_pair := heven
    parameter_pos := hm
    model := e
    centralizers := hcentralizers
    degree := hdegree
    fixed := hfixed }
  obtain ⟨f, hf⟩ := d.centralizer_embedding
  obtain ⟨g⟩ := d.localGeometry f hf
  exact d.false_of_geometry g d.torus_semiregular f hf

end BenderSuzuki.ZD
