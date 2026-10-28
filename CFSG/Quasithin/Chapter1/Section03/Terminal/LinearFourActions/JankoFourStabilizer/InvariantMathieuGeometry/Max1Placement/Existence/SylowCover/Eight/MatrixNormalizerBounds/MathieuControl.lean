module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Definitions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Marking
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.Stabilizer

/-!
# Ambient normalizers of small kernel subgroups containing a 2B involution

A conjugate of the max1 kernel seed that lies in the kernel can be carried
back to the seed inside max1: its other kernel orbit is excluded by the
unequal full centralizer orders. The remaining correction belongs to the
full seed centralizer, already proved to lie in max1. This controls the full
ambient normalizer of any kernel subgroup meeting the seed class.

If that subgroup has order less than 2048, the bound is strict. Equality
would make it normal in max1 and force it to contain the normal closure of
the seed, namely the entire kernel. The literal row-one consumer below
retains only the finite membership, conjugacy and cardinal certificates.

Source context: GLS3 Table 5.3i and the Sylow-overgroup analysis cited in
Aschbacher–Smith A.3.12. The imported kernel-orbit and centralizer proofs
use the literal ATLAS max1 words; no ambient simplicity or group order is used.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.Cardinality Janko4.Max1AmalgamRigidity
open Janko4.Simplicity.Max1Fusion
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed
local notation "t" => (localKernelSeed matrixA_mul_self matrixB_pow_four : Model)

/-- A transporter of the marked seed into the actual kernel lies in max1. -/
theorem seed_transporter_mem_max1 (g : Model) (hg : g * t * g⁻¹ ∈ E) : g ∈ M := by
  have ht : t ≠ 1 := by
    intro he
    have ho := AdequateLocal.seed_order
    change orderOf t = 2 at ho
    rw [he, orderOf_one] at ho
    omega
  obtain ⟨z, hz, he⟩ := hg
  change (z : Model) = g * t * g⁻¹ at he
  have hz' : z ≠ 1 := by
    intro hz'
    have hconj : g * t * g⁻¹ = 1 := by simpa [hz'] using he.symm
    exact ht ((MulAut.conj g).injective (hconj.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨m, hm | hm⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four z hz hz'
  · have hmt : t = ((m : Model) * g) * t * ((m : Model) * g)⁻¹ := by
      have h := congrArg M.subtype hm
      change t = (m : Model) * (z : Model) * (m : Model)⁻¹ at h
      rw [he] at h
      simpa only [mul_inv_rev, mul_assoc] using h
    have hc : (m : Model) * g ∈ InvolutionCentralizers.Second.ambientCentralizer := by
      apply mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp hmt.symm
    have hmG := InvolutionCentralizers.Second.ambient_le_max1 hc
    simpa only [inv_mul_cancel_left] using M.mul_mem (M.inv_mem m.property) hmG
  · have htp : IsConj t (kernelPair matrixA_mul_self matrixB_pow_four : Model) := by
      refine isConj_iff.mpr ⟨(m : Model) * g, ?_⟩
      have h := congrArg M.subtype hm
      change (kernelPair matrixA_mul_self matrixB_pow_four : Model) =
        (m : Model) * (z : Model) * (m : Model)⁻¹ at h
      rw [he] at h
      simpa only [mul_inv_rev, mul_assoc] using h.symm
    exact (AdequateLocal.seed_not_isConj_pair htp).elim

/-- The full ambient normalizer, not just its intersection with max1, is bounded. -/
theorem normalizer_le_max1_of_kernel_seed
    (V : Subgroup Model) (hVE : V ≤ E)
    (hseed : ∃ u ∈ V, IsConj t u) : normalizer (V : Set Model) ≤ M := by
  obtain ⟨u, hu, htu⟩ := hseed
  obtain ⟨k, hk'⟩ := isConj_iff.mp htu
  have hkM : k ∈ M := seed_transporter_mem_max1 k (hk'.symm ▸ hVE hu)
  intro g hg
  have hconj : (g * k) * t * (g * k)⁻¹ ∈ E := by
    simpa only [mul_inv_rev, mul_assoc, ← hk'] using
      hVE ((mem_normalizer_iff.mp hg u).mp hu)
  have hgk := seed_transporter_mem_max1 (g * k) hconj
  simpa only [mul_inv_cancel_right] using M.mul_mem hgk (M.inv_mem hkM)

/-- A small kernel subgroup meeting the seed class cannot be normal in max1. -/
theorem not_max1_le_normalizer_of_kernel_seed
    (V : Subgroup Model) (hVE : V ≤ E)
    (hseed : ∃ u ∈ V, IsConj t u) (hcard : Nat.card V < 2048) :
    ¬ M ≤ normalizer (V : Set Model) := by
  intro hMN
  obtain ⟨u, hu, htu⟩ := hseed
  obtain ⟨k, hk'⟩ := isConj_iff.mp htu
  have hkM : k ∈ M := seed_transporter_mem_max1 k (hk'.symm ▸ hVE hu)
  have htV : t ∈ V := by
    have h := (mem_normalizer_iff.mp (hMN (M.inv_mem hkM)) u).mp hu
    simpa only [← hk', inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  have hVM : V ≤ M := hVE.trans E_le_M
  let W : Subgroup M := V.subgroupOf M
  let : W.Normal := normal_subgroupOf_of_le_normalizer hMN
  have hKW : K ≤ W := by
    change localKernel matrixA_mul_self matrixB_pow_four ≤ W
    unfold localKernel
    exact normalClosure_le_normal (Set.singleton_subset_iff.mpr htV)
  have hEV : E ≤ V := by
    rw [← map_subgroupOf_eq_of_le hVM]
    exact map_mono hKW
  have hEcard : Nat.card E = 2048 := by
    rw [card_map_of_injective M.subtype_injective]
    exact localKernel_card matrixA_mul_self matrixB_pow_four
  have := card_le_of_le hEV
  omega

/-- The fixed-vector certificate proves properness of literal max1. -/
theorem literal_max1_ne_top : M ≠ (⊤ : Subgroup Model) := by
  intro ht
  exact cosetVectorStabilizer_ne_top matrixB_pow_four
    (top_unique (ht ▸ max1Subgroup_le_cosetVectorStabilizer matrixA_mul_self matrixB_pow_four))

/-- Both inclusions needed for the strict proper-overgroup alternative. -/
theorem normalizer_lt_max1_of_kernel_seed
    (V : Subgroup Model) (hVE : V ≤ E)
    (hseed : ∃ u ∈ V, IsConj t u) (hcard : Nat.card V < 2048) :
    normalizer (V : Set Model) < M :=
  lt_of_le_not_ge (normalizer_le_max1_of_kernel_seed V hVE hseed)
    (not_max1_le_normalizer_of_kernel_seed V hVE hseed hcard)

/-- The actual row-one application. Its three finite premises remain with
this task's matrix-certificate assembly; none asserts the normalizer bound. -/
theorem row_one_of_kernel_certificates
    (hUE : U 1 ≤ E) (hseed : ∃ u ∈ U 1, IsConj t u) (hcard : Nat.card (U 1) = 8) :
    EightNormalizerAlternative (U 1) := by
  right
  exact ⟨M, normalizer_lt_max1_of_kernel_seed (U 1) hUE hseed (by omega), literal_max1_ne_top⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
