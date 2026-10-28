module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.SourceData
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Separate local geometry and fiber inputs for Lemma 12.8

The local model calculation determines the fixed-coset degree and matches its
exponent with the actual centralizing extension. Independently, counting the
mixed-pair fibers uses the literal sizes of the fixed distinguished subgroup
and fixed-coset set. Neither input contains the ambient degree formula.
`Numerics` assembles them using the supported Thompson order formula.

These are explicit proof obligations. Their producers must supply every field
before the pointwise numerical theorem is complete.
Source: GLS4, Chapter 2, Lemmas 12.3–12.4 and the proof of Lemma 12.8,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The local orbit/model calculation, before counting the ambient group. -/
public structure ResidualCentralizerPointGeometry
    (Z : Set G) (M : Subgroup G) (z t v : G) (k i : ℕ) : Prop where
  exponent_ge : 2 ≤ k
  kind : i = 1 ∨ i = 2 ∨ i = 3
  suzuki_odd : i = 2 → Odd k
  fixed_distinguished :
    Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k
  fixed_cosets : Nat.card {beta : G ⧸ M // v • beta = beta} = (2 ^ k) ^ i + 1
  central_model : v ∈ centralizer (residualGenerated M z t : Set G) →
    ResidualCentralizerModelCase Z M z t v k i

/-- The two actual Thompson fiber counts. The moving count is multiplied by
the actor centralizer order, avoiding division and keeping integrality. The
vanishing of the distinguished fiber in the centralizing case is proved from
support in `Numerics.Support`, rather than assumed here. -/
public structure ResidualCentralizerFiberCounts
    (Z : Set G) (M : Subgroup G) (z v : G) : Prop where
  at_actor :
    let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
    let f := Nat.card {beta : G ⧸ M // v • beta = beta}
    kappa z v v = (q - 1) * f * ((f - 1) * (q - 1) + 1)
  at_distinguished :
    v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G) →
    let q := Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G)
    let f := Nat.card {beta : G ⧸ M // v • beta = beta}
    (q + 1) * kappa z v z * Nat.card (centralizer ({v} : Set G)) = Nat.card M * f * q

end BenderSuzuki.ZD
