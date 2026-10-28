module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannFactor
public import CFSG.Quasithin.Chapter10.SourceA5ZeroPairKernelSplit
public import Theory.GroupTheory.PairCoreCommutatorSplit

/-!
# The zero-center paired core is the sum of its two commutator layers

The source kernel split can be rewritten using the ambient-core commutator
identity for each original block.  This is the structural input used by the
remaining quotient-coordinate assembly of the Baumann centralizer factors.
Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_core_commutator_split
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧
      let U := D.moduleSubgroup.subgroupOf H
      let A := L.subgroupOf H
      let B := A.map (MulAut.conj t).toMonoidHom
      U = ⁅U, B⁆ ⊔ ⁅U, A⁆ := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let A := L.subgroupOf H
  obtain ⟨t, ht, hsplit⟩ := source_a5_zero_pair_kernel_split D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hA : IsBlock A :=
    (source_a5_original_block_of_baumann_not_controlled D e hn hout).1
  have hB : IsBlock B := hA.map_equiv (MulAut.conj t)
  refine ⟨t, ht, ?_⟩
  exact pair_core_commutator_split hu hA hB (by simpa only [B, A, H, sup_comm] using hsplit)

end CFSG.Quasithin.Chapter10
