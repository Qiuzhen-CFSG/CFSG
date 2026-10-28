module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.Support
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.Shearing
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.FiberCount
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import Theory.GroupTheory.TwoInvolutionClassOrder.SingleSupport

/-!
# The linear coset degree and stabilizer order

The single shearing fusion supplies mixed-fiber support. Thompson counting,
the exact fiber cardinality and the proved centralizer index give the coset
degree `(q+1)(q(q-1)+1) = q³+1`. The existing doubly transitive action then gives
`|M| = q³|D|`, the order consumed by the localization argument.

The final two theorems select the actual involution in `C_G(L)` and discharge
both the shearing fusion and the fiber count using their proved producers.
No degree, stabilizer order, or exhaustion of ambient involution classes is
assumed. The earlier conditional counting interfaces remain available.
The higher source owner retains discharge of the explicitly permitted
centralizer-closure collapse.
Source: GLS, Volume 4, Chapter 2, Lemmas 12.8(a), 12.10(a), and 15.2(f),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The linear degree follows from the single shearing fusion and the actual
mixed-pair fiber count. The final assembly below supplies both inputs. -/
public theorem linear_coset_degree_of_fusion_and_fiber
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z))
    (hcount : kappa z u u = (2 ^ n - 1) * (2 ^ n + 1) *
      (2 ^ n * (2 ^ n - 1) + 1)) :
    Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1 := by
  have hs := linear_halfOrder_support_of_one_fusion h r hz hzM ht htM hL hAL huJ hu hcollapse hshear
  have hcG := card_eq_of_halfOrder_support z u hs
  have hcM := linear_distinguished_centralizer_card h.disconnected r hz hzM ht htM hL hn e hAL
  have hnum (q : ℕ) (hq : q ≠ 0) : (q + 1) * (q * (q - 1) + 1) = q ^ 3 + 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    ring
  have hG : Nat.card G = ((2 ^ n) ^ 3 + 1) * Nat.card M := by
    rw [hcG, hcount, hcM, ← hnum (2 ^ n) (by positivity)]
    ring
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := M))
  exact (M.card_eq_card_quotient_mul_card_subgroup).symm.trans hG

/-- The same counting premises now supply the exact order used by local control. -/
public theorem linear_stabilizer_card_of_fusion_and_fiber
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z))
    (hcount : kappa z u u = (2 ^ n - 1) * (2 ^ n + 1) *
      (2 ^ n * (2 ^ n - 1) + 1)) :
    Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) :=
  linear_stabilizer_card_of_degree ha htM
    (linear_coset_degree_of_fusion_and_fiber h r hz hzM ht htM hL hn e hAL huJ hu hcollapse hshear hcount)
end BenderSuzuki.ZD

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Select the actual centralizer involution and apply two explicit counting
inputs. The final assembly below proves these inputs from the local geometry. -/
public theorem linear_degree_and_stabilizer_card_of_counting
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hshear : ∀ u : G, u ∈ centralizer (residualGenerated M z t : Set G) →
      PFAppendixIII.IsInvolution u → IsConj u (u * z))
    (hcount : ∀ u : G, u ∈ centralizer (residualGenerated M z t : Set G) →
      PFAppendixIII.IsInvolution u → IsConj u (u * z) →
      kappa z u u = (2 ^ n - 1) * (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1) + 1)) :
    Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1 ∧
      Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) := by
  obtain ⟨u, huJ, huD, hu, _⟩ := linear_counting_involution h.disconnected hz hzM htM hJ
  have hs := hshear u huJ hu
  have hd := linear_coset_degree_of_fusion_and_fiber h r hz hzM ht htM hL hn e hAL
    huJ hu (hcollapse u huD hu) hs (hcount u huJ hu hs)
  exact ⟨hd, linear_stabilizer_card_of_degree ha htM hd⟩

/-- GLS4, Lemmas 12.8(a) and 12.10(a), in the commuting linear case:
the actual coset degree is `q³+1`. Shearing, mixed-fiber support and its
cardinality are proved; only the permitted earlier centralizer collapse remains. -/
public theorem linear_coset_degree_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    Nat.card (G ⧸ M) = (2 ^ n) ^ 3 + 1 := by
  obtain ⟨u, huJ, huD, hu, _⟩ := linear_counting_involution h.disconnected hz hzM htM hJ
  have hcl := hcollapse u huD hu
  have hs := linear_shearing_of_centralizerClosure h r ha hz hzM ht htM hL hAL hJ
    hcollapse huJ hu
  have hc := linear_kappa_of_one_fusion h.disconnected r hz hzM ht htM hL hn e huJ hu hcl hs
  exact linear_coset_degree_of_fusion_and_fiber h r hz hzM ht htM hL hn e hAL huJ hu hcl hs hc

/-- Apply the proved degree to the actual doubly transitive coset action.
This discharges the stabilizer-order premise used in GLS4, Lemma 15.2(f). -/
public theorem linear_stabilizer_card_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) :=
  linear_stabilizer_card_of_degree ha htM
    (linear_coset_degree_of_centralizerClosure h r ha hz hzM ht htM hL hn e hAL hJ hcollapse)
end BenderSuzuki.ZD
