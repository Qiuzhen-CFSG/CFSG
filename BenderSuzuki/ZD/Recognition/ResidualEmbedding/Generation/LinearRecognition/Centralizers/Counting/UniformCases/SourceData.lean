module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts

/-!
# Earlier inputs to the uniform centralizer alternatives

The two independent inputs are the Thompson counts of Lemma 12.8 and the
ambient action consequences of Corollary 7.12. The numerical witness keeps
the noncentral field-action case; centralization is not an input. Its
centralizing model alternatives connect the exponent in the count to the
actual models and centralizer closures from Lemma 12.3.

These are proof obligations, not assertions that the earlier source results
have been proved. `UniformCases` must discharge both inputs before claiming
Lemma 12.9 or the unconditional uniform alternatives. The unitary alternative
is retained: its later exclusion belongs to Section 13.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Corollary 7.12 and Lemmas 12.3,
12.8–12.10.
-/

namespace BenderSuzuki.ZD
open Subgroup
open _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The model corresponding to the exponent `i` in Lemma 12.8, once the
actor centralizes `L`. These are pointwise alternatives, before uniformity. -/
@[expose] public def ResidualCentralizerModelCase
    (Z : Set G) (M : Subgroup G) (z t v : G) (k i : ℕ) : Prop :=
  (i = 1 ∧ centralizerClosure Z v = residualGenerated M z t ∧
    Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup k)) ∨
  (i = 2 ∧ centralizerClosure Z v = residualGenerated M z t ∧
    ∃ m : ℕ, 1 ≤ m ∧ k = 2 * m + 1 ∧
      Nonempty (residualGenerated M z t ≃* SuzukiMatrixGroup m)) ∨
  (i = 3 ∧ residualGenerated M z t < centralizerClosure Z v ∧
    IsUnitaryCentralizerCoverAt k (centralizerClosure Z v) ∧
      Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup k))

/-- The literal fixed-coset and mixed-fiber numerical conclusions of
Lemma 12.8 for one involution, with `qᵥ = 2^k`. The noncentral formula is
cross-multiplied so it retains the integrality assertion used in 12.9. -/
public structure ResidualCentralizerNumericalWitness
    (Z : Set G) (M : Subgroup G) (z t v : G) (k i : ℕ) : Prop where
  exponent_ge : 2 ≤ k
  kind : i = 1 ∨ i = 2 ∨ i = 3
  suzuki_odd : i = 2 → Odd k
  fixed_distinguished :
    Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k
  fixed_cosets : Nat.card {beta : G ⧸ M // v • beta = beta} = (2 ^ k) ^ i + 1
  central_degree : v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) →
    Nat.card (G ⧸ M) = ((2 ^ k) ^ i + 1) * ((2 ^ k) ^ i * (2 ^ k - 1) + 1)
  moving_degree : v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G) →
    Nat.card (closure (Z ∩ (M : Set G))) = (2 ^ k) ^ 2 ∧
      (2 ^ k + 1) * Nat.card (G ⧸ M) =
        ((2 ^ k) ^ i + 1) * ((2 ^ k) ^ i * (2 ^ k - 1) + 2 ^ k + 1)
  central_model : v ∈ centralizer (residualGenerated M z t : Set G) →
    ResidualCentralizerModelCase Z M z t v k i

/-- The pointwise Lemma 12.8 producer. Neither uniformity nor centralization
of the actors is assumed by this interface. -/
@[expose] public def ResidualCentralizerNumerics
    (Z : Set G) (M : Subgroup G) (z t : G) : Prop :=
  ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
    ∃ k i : ℕ, ResidualCentralizerNumericalWitness Z M z t v k i

/-- Earlier action consequences used by Lemma 12.9: the proper local orbit
cannot exhaust the ambient action, and primes dividing the residual torus
order give the Corollary 7.12 fixed-point congruence. -/
public structure ResidualCentralizerArithmeticInput
    (Z : Set G) (M : Subgroup G) : Prop where
  degree_gt : Nat.card (closure (Z ∩ (M : Set G))) + 1 < Nat.card (G ⧸ M)
  congruence : ∀ p : ℕ, p.Prime → p ∣ Nat.card (closure (Z ∩ (M : Set G))) - 1 →
    Nat.ModEq p (Nat.card (G ⧸ M)) 2

end BenderSuzuki.ZD
