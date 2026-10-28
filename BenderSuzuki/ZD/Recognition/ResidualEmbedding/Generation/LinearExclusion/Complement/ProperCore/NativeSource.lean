module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.PairResidual
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Torus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.InvolutionBounds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.TorusNonsquares

/-!
# The proper two-core branch of the linear exclusion

For the actual proper residual group L ≃ PSL₂(2ⁿ), suppose the two order
formulas of Lemma 15.6 hold: |C_G(L)| = 2 and |⟨C_G(L)ᴹ⟩| = 2q².
If this normal closure R is smaller than O₂(M), the earlier centralizer
collapse gives local control and the torus section. The involution census
constructs the abelian index-two base, and the nonsquare argument makes
the actual commutator kernel a normal complement to D ∩ O₂(M).
It therefore gives a normal complement to D in M.

The cyclic outer action also makes O²(D) proper, contradicting the focal
conclusion O²(M) = M. Consequently the order formulas force R = O₂(M).
Only the earlier source order formulas remain explicit: no involution base,
localization, torus, complement, or target contradiction is assumed.

Source: GLS, Volume 4, Chapter 2, Lemma 15.7, the proper-containment case,
and the final contradiction of Proposition 15.1.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The complete proper-containment branch of Lemma 15.7, after the two
order formulas in Lemma 15.6. The complement is normal inside M. -/
public theorem Context.pair_normalComplement_of_properCore
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M) :
    ∃ N : Subgroup M, N.Normal ∧ N ≤ pCore 2 M ∧
      ((residualPairStabilizer M t).subgroupOf M).IsComplement' N := by
  have hcollapse : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      centralizerClosure Z v = residualGenerated M z t :=
    fun _ hvD hv => d.centralizer_closure hvD hv
  obtain ⟨hlocal, hMcard⟩ := linear_involution_localization_and_card_of_centralizerClosure
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le hJ hcollapse
  obtain ⟨hKcard, hAfixed⟩ := linear_distinguishedClosure_torus_geometry
    d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model d.distinguished_le
  obtain ⟨hDV, hfixed⟩ := linear_localControl_of_localization_and_orders
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter hJ hR hproper d.pair_normalizes hlocal hAfixed hKcard hMcard
  obtain ⟨hAB, hBcard, hsq, htrans⟩ :=
    linear_involutionBase_torus_section_of_centralizerClosure
      d.minimal d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
      d.proper d.parameter d.model hJ hR d.distinguished_le hfixed hcollapse
  obtain ⟨hcount, hbound⟩ := linear_involutionBase_bounds_of_centralizerClosure_and_section
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.parameter d.model hJ hR d.distinguished_le d.pair_normalizes
    hDV hcollapse hAB hsq
  obtain ⟨B, hBR, hindex, hcomm, hnon, hout, hdis⟩ :=
    linear_involutionBase_of_torus_section_and_involution_bounds
      d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
      d.proper d.parameter d.model hJ hR d.distinguished_le hfixed
      ⟨hAB, hBcard⟩ htrans hcount hbound
  obtain ⟨hnormal, habel, hdisjoint⟩ :=
    linearCommutatorKernel_properties_of_localization_and_orders
      d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
      d.proper d.parameter d.model hJ hR hproper d.distinguished_le d.pair_normalizes
      hDV hfixed B hBR hindex hcomm hnon hout hdis hlocal hAfixed hMcard
  obtain ⟨_, N, hN, hNV, hsplit⟩ := linear_twoCore_complement_of_commutatorKernel
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.pair_normalizes hDV hfixed hnormal habel hdisjoint
  exact ⟨N, hN, hNV, linear_pair_complement_of_twoCore_complement N hNV hDV hsplit⟩

/-- The source proper-core task's internal complement, with its supplement
identity. Both are obtained from the constructed normal complement in M. -/
public theorem Context.twoCore_complement_of_properCore
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      ∃ N : Subgroup M, N.Normal ∧ N ≤ pCore 2 M ∧
        (((residualPairStabilizer M t).subgroupOf M).subgroupOf (pCore 2 M)).IsComplement'
          (N.subgroupOf (pCore 2 M)) := by
  obtain ⟨N, hN, hNV, hsplit⟩ := d.pair_normalComplement_of_properCore hJ hR hproper
  refine ⟨?_, N, hN, hNV, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨⟨a, b⟩, rfl⟩ := hsplit.2 x
    exact Subgroup.mul_mem _ (mem_sup_left a.property) (mem_sup_right (hNV b.property))
  · refine ⟨Subgroup.mul_injective_of_disjoint ?_, ?_⟩
    · apply disjoint_def.mpr
      intro x hxD hxN
      exact Subtype.ext (disjoint_def.mp hsplit.disjoint hxD hxN)
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ := hsplit.2 (x : M)
      have haV : (a : M) ∈ pCore 2 M := by
        have he : (a : M) = (x : M) * (b : M)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hab
        rw [he]
        exact (pCore 2 M).mul_mem x.property ((pCore 2 M).inv_mem (hNV b.property))
      exact ⟨(⟨⟨a, haV⟩, a.property⟩, ⟨⟨b, hNV b.property⟩, b.property⟩), Subtype.ext hab⟩

/-- The proper-containment branch contradicts the already proved source
focal-transfer conclusion, without an assumed residual of the pair group. -/
public theorem Context.properCore_false
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M) : False := by
  obtain ⟨N, hN, _, hsplit⟩ := Context.pair_normalComplement_of_properCore d hJ hR hproper
  exact linearExclusion_of_centralizer_two_and_normalComplement
    d.minimal d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper d.even_pair d.model hJ N hN hsplit

/-- After Lemma 15.6, only the equality case of Lemma 15.7 remains.
The literal normal closure of C_G(L) is the whole two-core of M. -/
public theorem Context.centralizerClosure_eq_twoCore_of_orders
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2) :
    linearCentralizerClosure M z t = pCore 2 M := by
  apply le_antisymm (linearCentralizerClosure_le_twoCore hR)
  by_contra hnot
  exact Context.properCore_false d hJ hR
    (lt_of_le_not_ge (linearCentralizerClosure_le_twoCore hR) hnot)

end BenderSuzuki.ZD.LinearExclusion
