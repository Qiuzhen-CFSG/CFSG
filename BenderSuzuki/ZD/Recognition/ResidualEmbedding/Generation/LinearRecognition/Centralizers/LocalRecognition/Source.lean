module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.CentralizingCovers.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.InvolutionAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.QuotientFactorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.Conjugacy

/-!
# The complete local centralizer conclusions of GLS Lemmas 12.3–12.4

The central-cover, involutory-action, odd-core quotient, conjugacy and set-product
arguments now supply every field of the local recognition contract. All use
the original proper residual subgroup and the distinguished two-point
stabilizer. The unitary-cover lift and the exclusion of fixed-field size two
are discharged by their source proofs.

Source: GLS IV, Chapter 2, Lemmas 12.3 and 12.4(b–e).
-/

namespace BenderSuzuki.ZD

open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- GLS IV, Chapter 2, Lemmas 12.3–12.4: all five local centralizer
conclusions, with the original quotient maps, field exponents and set product. -/
public theorem proper_residualGenerated_centralizer_local_data
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ResidualCentralizerLocalData Z M z t where
  centralizing_extension :=
    proper_residualGenerated_centralizing_extension h r ha hz hzM ht htM hL heven
  involution_action :=
    proper_residualGenerated_involution_action h r ha hz hzM ht htM hL heven
  quotient_models :=
    proper_residualGenerated_centralizer_quotient_models h r ha hz hzM ht htM hL heven
  punctured_coset_conjugacy := by
    intro v hvD hv a haA hav ha1 b hbA hbv hb1
    exact proper_pair_involution_punctured_coset_conjugacy h r ha hz hzM ht htM
      hL heven hvD hv haA hav ha1 hbA hbv hb1
  centralizer_factorization :=
    proper_residualGenerated_centralizer_factorization h r ha hz hzM ht htM hL heven

end BenderSuzuki.ZD
