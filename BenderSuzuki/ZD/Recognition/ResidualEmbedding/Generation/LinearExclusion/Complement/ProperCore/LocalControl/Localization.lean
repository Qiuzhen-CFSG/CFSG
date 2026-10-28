module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree

/-!
# Applying linear centralizer localization to local control

The distinguished centralizer-closure premise proves the involution
localization required by `linear_localControl_of_localization_and_orders`.
The mixed-involution count proves the degree `q³+1`, and double transitivity
converts it into the exact order premise. The final application supplies
both proved premises to that actual consumer.

The original degree-conditional interfaces are retained. The final two
theorems discharge that counting premise using GLS4, Chapter 2, Lemma 12.10(a).
The torus premises belong to the sibling torus argument, and the earlier
closure-collapse premise is Proposition 13.1. Their source assembly remains
with the proper-core local-control owner.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.8–12.10 and 15.2.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The two literal premises consumed by local control, with the degree
still displayed as the remaining independent counting input. -/
public theorem linear_involution_localization_and_card_of_centralizerClosure_and_degree
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hdegree : Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1) :
    (pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M) ∧
    Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) :=
  ⟨linear_involution_localization_of_centralizerClosure h r hz hzM ht htM hL hn e hAL
      hJ hcollapse,
    linear_stabilizer_card_of_degree ha htM hdegree⟩

/-- Supply the proved localization and the degree-to-order calculation to
the published local-control consumer. The source degree and sibling torus
inputs remain explicit until their respective producers are assembled. -/
public theorem linear_localControl_of_centralizerClosure_and_degree
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hdegree : Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
        centralizer ({k} : Set M) = ⊥)
    (hKcard : Nat.card ((residualPairStabilizer M t ⊓
      residualGenerated M z t).subgroupOf M) = 2 ^ n - 1) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      pCore 2 M ⊓ centralizer
        (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  obtain ⟨hlocal, hMcard⟩ :=
    linear_involution_localization_and_card_of_centralizerClosure_and_degree
      h r ha hz hzM ht htM hL hn e hAL hJ hcollapse hdegree
  exact linear_localControl_of_localization_and_orders h r hz hzM ht htM hL hn hJ hR
    hproper hDN hlocal hAfixed hKcard hMcard

/-- The two literal local-control premises, with the linear coset degree
proved by mixed-involution counting. The only extra earlier-source input
is the permitted centralizer-closure collapse. -/
public theorem linear_involution_localization_and_card_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    (pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M) ∧
    Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) :=
  linear_involution_localization_and_card_of_centralizerClosure_and_degree
    h.disconnected r ha hz hzM ht htM hL hn e hAL hJ hcollapse
    (linear_coset_degree_of_centralizerClosure h r ha hz hzM ht htM hL hn e hAL hJ hcollapse)

/-- Supply the proved localization and stabilizer order to the published
local-control consumer. The sibling torus inputs and earlier centralizer
collapse remain with the source assembly owner. -/
public theorem linear_localControl_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
        centralizer ({k} : Set M) = ⊥)
    (hKcard : Nat.card ((residualPairStabilizer M t ⊓
      residualGenerated M z t).subgroupOf M) = 2 ^ n - 1) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      pCore 2 M ⊓ centralizer
        (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  obtain ⟨hlocal, hMcard⟩ :=
    linear_involution_localization_and_card_of_centralizerClosure
      h r ha hz hzM ht htM hL hn e hAL hJ hcollapse
  exact linear_localControl_of_localization_and_orders h.disconnected r hz hzM ht htM hL hn
    hJ hR hproper hDN hlocal hAfixed hKcard hMcard
end BenderSuzuki.ZD
