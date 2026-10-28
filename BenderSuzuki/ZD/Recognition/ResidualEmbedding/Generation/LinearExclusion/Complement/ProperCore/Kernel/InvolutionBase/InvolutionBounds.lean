module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.InvolutionBounds.Census
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.ElementaryRank

/-!+# Involution bounds for the distinguished base

Write `q = 2^n`, `A = ⟨Z ∩ M⟩`, `L = residualGenerated M z t`,
`D = residualPairStabilizer M t`, `J = C_G(L)`, `R = ⟨Jᴹ⟩`, and
`B = [R, D ∩ L]`, with R and B taken internally in M.

The census proves that the nonidentity element of J has q² distinct
M-conjugates in R outside A. Together with A these give at least q² + q
square-one elements, including the identity. Localization rules out
exponent two in R. A free torus orbit of a nontrivial square then supplies
q(q-1) noninvolutions, so the census exhausts the involutions outside A.
An elementary subgroup crossing A can therefore be conjugated into the
centralizer of the involution of J. Its actual conjugation action on L has
kernel contained in J; the PSL₂ automorphism rank bound gives order at most 2q.

The theorem assembles precisely the two bounds consumed by
`linear_involutionBase_of_torus_section_and_involution_bounds`.
Of the earlier section premises it needs only A ≤ B and the square
containment in A. The order of B and torus transitivity on B/A remain
inputs to that later extraction, rather than to these bounds.
The centralizer-collapse and section premises remain to be discharged by
the source assembly owner. No abelian-base or noninvolution-in-B conclusion
is assumed here.

Source: GLS, Volume 4, Chapter 2, end of Lemma 15.6 and first paragraph
of Lemma 15.7, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- The two literal involution bounds needed for base extraction, from the
permitted centralizer collapse and earlier section facts. The distinguished
closure and all subgroup restrictions are retained exactly. -/
public theorem linear_involutionBase_bounds_of_centralizerClosure_and_section
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAB : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M) :
    ((2 ^ n) ^ 2 + 2 ^ n ≤ Nat.card {x : linearCentralizerClosure M z t // x ^ 2 = 1}) ∧
      (∀ E : Subgroup M, E ≤ linearCentralizerClosure M z t →
        (∀ x ∈ E, x ^ 2 = 1) → ¬ E ≤ (closure (Z ∩ (M : Set G))).subgroupOf M →
        Nat.card E ≤ 2 * 2 ^ n) := by
  exact ⟨linear_square_one_census_of_centralizerClosure_and_section
      h r ha hz hzM ht htM hL hn e hJ hR hAL hDN hDV hcollapse hAB,
    linear_elementary_crossing_card_le_of_centralizerClosure_and_section
      h r ha hz hzM ht htM hL hn e hAL hJ hR hDN hDV hcollapse hAB hsq⟩

end BenderSuzuki.ZD
