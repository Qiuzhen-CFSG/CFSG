module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Torus

/-!
# Applying the distinguished-closure torus geometry to local control

The literal subgroups and singleton centralizers from `Torus` discharge both
`hKcard` and `hAfixed` in the published conditional local-control theorem.
The centralizer localization and remaining order formulas stay explicit;
the proper-core local-control assembly owns their independent proofs.

Source: GLS, Volume 4, Chapter 2, the proper-core argument in Lemmas
15.6--15.7, using Chapter 4, Lemma 3.2(b--e).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- Local control with the torus order and every element's fixed-point premise
discharged by the actual binary PSL₂ model. -/
public theorem linear_localControl_of_localization_and_linear_model
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hlocal : pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hMcard : Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t)) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      pCore 2 M ⊓ centralizer
        (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  obtain ⟨hKcard, hAfixed⟩ :=
    linear_distinguishedClosure_torus_geometry h r hz hzM ht htM hL hn e hAL
  exact linear_localControl_of_localization_and_orders h.disconnected r hz hzM ht htM hL hn
    hJ hR hproper hDN hlocal hAfixed hKcard hMcard

end BenderSuzuki.ZD
