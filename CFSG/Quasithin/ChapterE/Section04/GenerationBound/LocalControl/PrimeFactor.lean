module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.CoreSpace
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PrimeQuotientSylowNormalizer

/-!
# The prime-order local quotient branch of E.4.2

Suppose F*(H/O₂(H)) has prime order. The generalized-Fitting
self-centralization theorem and the cyclic automorphism argument show that
every normal subgroup of H outside O₂(H), joined with a Sylow two-subgroup,
is normal in H. Self-centralization is supplied by the proved intrinsic
generalized-Fitting bridge in Chapter B; it is not an additional hypothesis.

Apply this to the kernel K of H on the invariant space formed inside its
two-core. Failure to normalize the earlier weak subgroup puts K outside
O₂(H). The CoreSpace Frattini argument then makes H preserve every later
weak fixed space. All kernel normality is relative to H, and the proof uses
the two-core O₂, without a residual commutator identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252). This proves the prime-order local invariance
branch; the quasisimple branch and the full E.4.2 assembly are separate.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A prime-order generalized Fitting subgroup of the two-core quotient
forces normal Sylow joins for normal subgroups outside the two-core. -/
theorem normal_sup_sylow_of_prime_generalizedFitting_quotient
    (hp : (Nat.card (generalizedFitting (G ⧸ pCore 2 G))).Prime)
    (N : Subgroup G) [N.Normal] (hn : ¬ N ≤ pCore 2 G) (S : Sylow 2 G) :
    (N ⊔ (S : Subgroup G)).Normal :=
  normal_sup_sylow_of_prime_order_selfCentralizing_quotient (pCore 2 G)
    pCore_isPGroup (generalizedFitting (G ⧸ pCore 2 G)) hp
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le N hn S

/-- The prime-order local quotient branch preserves all weak fixed spaces
from corank j + m₂(H/O₂(H)) onwards. -/
theorem eventual_invariance_of_prime_generalizedFitting
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j : ℕ}
    (hmk : j + primeRank 2 (H ⧸ pCore 2 H) ≤ k)
    (hp : (Nat.card (generalizedFitting (H ⧸ pCore 2 H))).Prime)
    (hn : ¬ H ≤ normalizer
      (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G)) :
    ∀ n, j + primeRank 2 (H ⧸ pCore 2 H) ≤ n →
      H ≤ subspaceStabilizer ρ
        (fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1)) n T)) := by
  let m := j + primeRank 2 (H ⧸ pCore 2 H)
  let K := subspaceKernel ρ (coreFixedSpace ρ k m H) H
  have hKH : K ≤ H := subspaceKernel_le ρ _ H
  have : (K.subgroupOf H).Normal := coreFixedSpace_kernel_normal ρ k m H
  have hK : ¬ K ≤ (pCore 2 H).map H.subtype :=
    coreFixedSpace_kernel_not_le_core ρ T H hTH le_rfl hmk hn
  have hNK : ¬ K.subgroupOf H ≤ pCore 2 H := by
    intro h
    apply hK
    simpa only [map_subgroupOf_eq_of_le hKH] using
      (map_mono (f := H.subtype) h)
  have hnormal := normal_sup_sylow_of_prime_generalizedFitting_quotient hp
    (K.subgroupOf H) hNK (T.subtype hTH)
  apply eventual_invariance_of_kernel_sup_normal ρ T H hTH k m
  change ((K ⊔ (T : Subgroup G)).subgroupOf H).Normal
  simpa only [subgroupOf_sup hKH hTH, Sylow.coe_subtype] using hnormal

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
