module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import Theory.GroupTheory.TorusInvolutionBase

/-!
# The involution-base extraction in the proper-core branch

Write `A = M°`, `R = ⟨Jᴹ⟩`, and `B = [R,K]`, all inside `M`.
The distinguished closure is retained literally. Once the source supplies
`A ≤ B`, `|B| = q²`, torus transitivity on `(B/A)#`, and its involution
bounds, counting forces every element of `R ∖ B` to square to one.
An outside involution inverts `B`, making it abelian. The order formulas
give index two, and `R = BJ` with `|J| = 2` gives `B ∩ J = 1`.

The theorem below is a conditional extraction, not a proof of the missing
source torus section or involution bounds. Their source constructions must
be supplied before the existence theorem requested by the kernel assembly
is complete. No normality or commutativity of `B` is an input.

Source: GLS, Volume 4, Chapter 2, end of Lemma 15.6 and first paragraph
of Lemma 15.7, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- Extract precisely the six base premises from the source torus section and
involution bounds. The witness is the literal `[R,K]`. The additional section,
transitivity and counting hypotheses remain source obligations. -/
public theorem linear_involutionBase_of_torus_section_and_involution_bounds
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hsection : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t ∧
      Nat.card (linearCommutatorKernel M z t) = (2 ^ n) ^ 2)
    (htrans : ∀ x ∈ linearCommutatorKernel M z t,
      x ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
      ∀ y ∈ linearCommutatorKernel M z t,
      y ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
      ∃ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
        ∃ a ∈ (closure (Z ∩ (M : Set G))).subgroupOf M, y = k * x * k⁻¹ * a)
    (hcount : (2 ^ n) ^ 2 + 2 ^ n ≤
      Nat.card {x : linearCentralizerClosure M z t // x ^ 2 = 1})
    (hbound : ∀ E : Subgroup M, E ≤ linearCentralizerClosure M z t →
      (∀ x ∈ E, x ^ 2 = 1) → ¬ E ≤ (closure (Z ∩ (M : Set G))).subgroupOf M →
      Nat.card E ≤ 2 * 2 ^ n) :
    ∃ B : Subgroup M, B ≤ linearCentralizerClosure M z t ∧
      B.relIndex (linearCentralizerClosure M z t) = 2 ∧
      (∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧
      (∃ b ∈ B, b ^ 2 ≠ 1) ∧
      (∀ x ∈ linearCentralizerClosure M z t, x ∉ B → x ^ 2 = 1) ∧
      Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let B := linearCommutatorKernel M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  have hBR : B ≤ R := linearCommutatorKernel_le_closure
  obtain ⟨hAsq, hAc, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h r hz hzM ht htM hL hn e hAL
  have hcentral : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro a ha b hb
    exact (mem_centralizer_iff.mp (hAc ha) b (linearCommutatorKernel_le_twoCore hR hb)).symm
  obtain ⟨hcomm, hnon, hout⟩ := abelian_noninvolution_profile_of_transitive_section
    R B A K hq hBR hsection.1 hR hsection.2 hAcard hAsq hcentral htrans hcount hbound
  have hindex : B.relIndex R = 2 := by
    have hc := (B.subgroupOf R).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv] at hc
    change Nat.card B * B.relIndex R = Nat.card R at hc
    rw [hsection.2, hR] at hc
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ n) ^ 2)
    exact hc.trans (Nat.mul_comm _ _)
  have hsplit : R = B ⊔ J := linearCentralizerClosure_eq_kernel_sup_centralizer
    h r hz hzM ht htM hL hR hfixed
  have hJcard : Nat.card J = 2 := linearCentralizer_subgroupOf_card h hz hzM hJ
  have hdis : Disjoint B J := by
    have hd := card_dvd_of_le (show B ⊓ J ≤ J from inf_le_right)
    rw [hJcard] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
    · exact disjoint_iff_inf_le.mpr ((B ⊓ J).eq_bot_iff_card.mpr hone).le
    · have hi : B ⊓ J = J := eq_of_le_of_card_ge inf_le_right (by rw [htwo, hJcard])
      have hJB : J ≤ B := hi.symm.le.trans inf_le_left
      have he : B = R := le_antisymm hBR (hsplit.le.trans (sup_le le_rfl hJB))
      rw [he, relIndex_self] at hindex
      contradiction
  exact ⟨B, hBR, hindex, hcomm, hnon, hout, hdis⟩

end BenderSuzuki.ZD
