module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Algebra

/-!
# Proper-core branch of the linear complement argument

The theorem below constructs the normal complement `[K,O₂(M)]` once the
local analysis supplies `M = DV`, `C_V(K) = J`, and the three required
properties of the actual commutator kernel `R₀ = [⟨Jᴹ⟩,K]`. The kernel
is normal in `M`, contains `[V,V]`, and misses `J`. The algebraic argument
therefore needs only an abelian quotient, rather than the full elementary
abelian quotient proved in the source.

Normalization of `L` by `D` is the earlier orbit-control obligation. It
gives normalization of `K = D ∩ L`. Coprimality then identifies `D ∩ V`
with `J`, and the quotient splitting in `Algebra` completes the construction.

This is conditional assembly. The proper-core case of GLS, Volume 4,
Chapter 2, Lemma 15.7 remains unfinished until the local supplement,
fixed-point equality and kernel properties are derived from its original
inputs. No additional local property is asserted as proved here.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 15.2–15.7.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Subgroup Theory.GroupTheory

/-- Assemble the proper-core complement from the local supplement and
centralizer analysis and the commutator kernel. All normality is relative
to `M`. These explicit premises remain obligations of source Lemma 15.7. -/
public theorem linear_twoCore_complement_of_commutatorKernel
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hR₀ : (linearCommutatorKernel M z t).Normal)
    (habel : ⁅pCore 2 M, pCore 2 M⁆ ≤ linearCommutatorKernel M z t)
    (hdis : Disjoint (linearCommutatorKernel M z t)
      ((centralizer (residualGenerated M z t : Set G)).subgroupOf M)) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      ∃ N : Subgroup M, N.Normal ∧ N ≤ pCore 2 M ∧
        (((residualPairStabilizer M t).subgroupOf M).subgroupOf (pCore 2 M)).IsComplement'
          (N.subgroupOf (pCore 2 M)) := by
  let : (linearCommutatorKernel M z t).Normal := hR₀
  have hDK := linear_pair_le_normalizer_inter_of_normalizes hDN
  have hinter := linear_pair_inf_twoCore_eq_of_fixed_centralizer h r hz hzM ht htM hL hDK hfixed
  let V := pCore 2 M
  let A := linearCommutatorKernel M z t
  let : IsMulCommutative (V ⧸ A.subgroupOf V) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      apply Subgroup.map_le_iff_le_comap.mp
      rw [map_commutator_eq, V.range_subtype]
      exact habel)
  refine ⟨hDV, linear_twoCore_complement_of_abelian_quotient h r hz hzM ht htM hL
    A hDV hDK (hfixed.trans hinter.symm) ?_⟩
  exact hinter.symm ▸ hdis

end BenderSuzuki.ZD
