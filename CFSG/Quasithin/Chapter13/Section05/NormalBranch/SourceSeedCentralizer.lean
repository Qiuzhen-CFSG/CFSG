module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreSplit
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The seed-centralizer bound in the normal A₆ branch

Normality of L₁ puts its commutators with C_H(V₃) inside L₁ and C_H(V₃).
The actual A₅ coordinates force those commutators into V. Three Subgroups
then makes [V,C_H(V₃)] centralize L₁. The index-two seed and its proved
centralizer inside U_H identify the bound as the original line V₁.

This discharges the centralizer hypothesis of F.9.5(6) from the original
normal-branch hypotheses, without an additional ambient plane-control input.
Source: Aschbacher–Smith,13.5.13(2) and13.5.15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSeedCentralizer
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d in
theorem source_seed_bound (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) :
    ⁅D.V,D.H⊓centralizer (D.Vplus:Set G)⁆≤D.V₁ := by
  obtain ⟨a,g,_,_,hK,hL,_,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  let C := D.H⊓centralizer (D.Vplus:Set G)
  have hLH : D.L₁≤D.H := le_sup_left.trans h.local_le
  have hHN : D.H≤normalizer (D.L₁:Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLH).mp hn
  have hCV : C≤normalizer (D.V:Set G) := by
    intro x hx
    exact (h.normalizer_control ⟨hx.1,(Subgroup.centralizer_le_normalizer _ hx.2)⟩).2
  have hLC : D.L₁≤normalizer (C:Set G) :=
    (le_inf (hLH.trans D.H.le_normalizer)
      ((le_sup_left.trans h.local_normalizes).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hcommL : ⁅C,D.L₁⁆≤D.L₁ :=
    le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hHN)
  have hcommC : ⁅C,D.L₁⁆≤C := le_normalizer_iff_commutator_le_left.mp hLC
  have hcommV : ⁅C,D.L₁⁆≤D.V := by
    intro x hx
    let k : NormalBranch.K D g.val := ⟨x,hL (hcommL hx)⟩
    have hk := SourceQuaternion.actor_eq_one_of_seed_centralizer d e g hK a hi k (hcommC hx).2
    have hkp : k∈pCore 2 (NormalBranch.K D g.val) := by
      rw [←restrictedActor_ker_eq_twoCore d hK a hi e]
      exact hk
    exact hS ▸ mem_map_of_mem (NormalBranch.K D g.val).subtype hkp
  have h1 : ⁅⁅C,D.L₁⁆,D.V⁆=⊥ := by
    let : IsMulCommutative D.V := h.elementary.toIsMulCommutative
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hcommV.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  have h2 : ⁅⁅D.L₁,D.V⁆,C⁆=⊥ := by
    rw [commutator_comm D.L₁ D.V,←hseed]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp inf_le_right)
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_rotate h1 h2)
  have hindex : D.Vplus.relIndex D.V=2 := by
    have hh := (D.Vplus.subgroupOf D.V).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe h.plus_le).toEquiv,d.seed_card,ReturningPlane.module_card d] at hh
    change (D.Vplus.subgroupOf D.V).index=2
    omega
  have hle : ⁅D.V,C⁆≤D.Vplus := commutator_le_of_normalized_index_two D.V D.Vplus C
    h.plus_le hindex hCV (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hUL : D.UH≤D.L₁ := (closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 _)
  rw [←SourceQuaternion.seed_centralizer d h e hseed hn hU g hK a hi]
  exact le_inf hle (hcentral.trans (centralizer_le hUL))

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSeedCentralizer
end
