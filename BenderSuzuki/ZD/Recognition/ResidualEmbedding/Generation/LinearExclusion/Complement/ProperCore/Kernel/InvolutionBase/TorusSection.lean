module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Containment
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Elementary
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Moving

/-!
# The torus section in the proper-core involution argument

Inside M write `A = M°`, `R = ⟨Jᴹ⟩`, `K = D ∩ L`, and `B = [R,K]`.
The distinguished layer lies in B, and every square in R lies in A.
Coprime action on the resulting elementary quotient R/A gives B order
q² and makes the actual torus K transitive on the nonidentity A-cosets
in B. The formula below retains the factor from A on the right.

This assembles the containment, elementary-quotient and moving-section
proofs, discharging the moving-section theorem's square premise. The
permitted earlier centralizer-closure collapse remains explicit; its
discharge and the subsequent involution bounds belong to the involution
base assembly. No normality or commutativity of B is assumed.

Source: GLS, Volume 4, Chapter 2, Lemma 15.6 and the opening of 15.7,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- The source elementary quotient and moving torus section, before the
involution count makes the commutator kernel abelian. The square premise of
the moving-section construction is supplied by the elementary-quotient proof. -/
public theorem linear_involutionBase_torus_section_of_centralizerClosure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t ∧
      Nat.card (linearCommutatorKernel M z t) = (2 ^ n) ^ 2 ∧
      (∀ x ∈ linearCentralizerClosure M z t,
        x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M) ∧
      ∀ x ∈ linearCommutatorKernel M z t,
        x ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
        ∀ y ∈ linearCommutatorKernel M z t,
          y ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
          ∃ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
            ∃ a ∈ (closure (Z ∩ (M : Set G))).subgroupOf M, y = k * x * k⁻¹ * a := by
  have hAB := linear_distinguishedClosure_le_commutatorKernel_of_centralizerClosure
    h r hz hzM ht htM hL hn e hJ hR hAL hcollapse
  have hsq := linear_involutionBase_elementary_quotient_of_centralizerClosure
    h r hz hzM ht htM hL hn e hJ hR hAL hcollapse
  obtain ⟨hcard, htrans⟩ := linear_involutionBase_moving_section_of_squares
    h r hz hzM ht htM hL hn e hJ hR hAL hfixed hcollapse hsq
  exact ⟨hAB, hcard, hsq, htrans⟩

end BenderSuzuki.ZD
