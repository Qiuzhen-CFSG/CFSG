module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveBlock
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration

/-!
# The original six-point commutator layer

In the normal case of source 13.5.15, the selected five-point subgroup normally
generates L. Its already identified two-core V therefore controls [O₂(L), L].
This identifies the actual block layer with the original module V.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixLayer
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem core_commutator_pair (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    ⁅D.L.pCoreIn 2,NormalBranch.K D g.val⁆≤D.V := by
  have hQK : D.L.pCoreIn 2≤normalizer (NormalBranch.K D g.val:Set G) :=
    (SourcePairResidual.local_core_le_LT_core h).trans (SourcePairResidual.twoCore_normalizes_pair h g)
  have hKQ : NormalBranch.K D g.val≤normalizer (D.L.pCoreIn 2:Set G) :=
    hK.trans (D.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.L (pCore 2 D.L)))
  rw [←hS]
  exact le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 D.L).to_le (le_normalizer_iff_commutator_le_left.mp hKQ))
    (le_normalizer_iff_commutator_le_right.mp hQK) (normalizer_commutator_ge_right _ _)

include d in
theorem pair_normalClosure (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (_hK : NormalBranch.K D g.val≤D.L) :
    normalClosure ((NormalBranch.K D g.val).subgroupOf D.L:Set D.L)=⊤ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D.L))
  have hk : f.ker=pCore 2 D.L := by
    ext l
    change e (QuotientGroup.mk' (pCore 2 D.L) l)=1↔l∈pCore 2 D.L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff l
  apply normalClosure_eq_top_of_pPerfect_simple_image
    ((pResidual_eq_top_iff 2 D.L).mp h.residual) f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hk ▸ pCore_isPGroup)
  intro hz
  have hle : (NormalBranch.K D g.val).subgroupOf D.L≤pCore 2 D.L := by
    rw [←hk]
    exact (Subgroup.map_eq_bot_iff _).mp hz
  have hbot : (D.UH.subgroupOf D.L).map (localMap d)=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [SourceBarred.local_kernel_eq_core d e]
    exact (subgroupOf_mono D.L (show D.UH≤NormalBranch.K D g.val from le_sup_left)).trans hle
  exact SourcePointCore.closure_image_nontrivial d h (closure_reduction h hseed hn).2.2 hU hbot

theorem block_layer_eq_module (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    (ChapterC.blockU D.L).map D.L.subtype=D.V := by
  have hVL : D.V≤D.L := hS ▸ (pCoreIn_le 2 _).trans hK
  let VL := D.V.subgroupOf D.L
  let : VL.Normal := (normal_subgroupOf_iff_le_normalizer hVL).mpr (le_sup_left.trans d.normalizes_V)
  have hvcore : D.V≤D.L.pCoreIn 2 :=
    hS ▸ SourceCoreProduct.core_le_local_core d e g hK a hi
  have hc : ⁅pCore 2 D.L,(NormalBranch.K D g.val).subgroupOf D.L⁆≤VL := by
    intro x hx
    have hh := mem_map_of_mem D.L.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hK] at hh
    exact core_commutator_pair h g hK hS hh
  have hbound := commutator_normalClosure_le_of_normal (pCore 2 D.L)
    ((NormalBranch.K D g.val).subgroupOf D.L) VL hc
  rw [pair_normalClosure d h e hseed hn hU g hK] at hbound
  apply le_antisymm
  · exact (map_mono hbound).trans_eq (map_subgroupOf_eq_of_le hVL)
  · have hcomm := SourceFiveSpan.module_commutator d hK a hi h hL hseed
    change D.V≤(⁅pCore 2 D.L,(⊤:Subgroup D.L)⁆).map D.L.subtype
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rw [←hcomm]
    exact commutator_mono hvcore hK

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixLayer
end
