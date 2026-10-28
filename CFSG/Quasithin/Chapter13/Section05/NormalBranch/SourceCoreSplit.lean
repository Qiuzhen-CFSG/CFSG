module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixBlock
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer

/-!
# The original two-core split after the A₅ block construction

Apply C.1.13(c) to the actual two-core of LT acting on the selected A₅
block. The Sylow centralizer identity identifies its centralizer factor
with C_T(K); irreducibility proves this factor meets V trivially. The final
consumer selects the pair from the original normal A₆ source hypotheses.

Source: Aschbacher–Smith, proof of13.5.15(7), printed p.920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreSplit
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

omit [Finite G] in
theorem pair_block_layer (g : D.L)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hc : ⁅D.V,NormalBranch.K D g.val⁆=D.V) :
    (ChapterC.blockU (NormalBranch.K D g.val)).map (NormalBranch.K D g.val).subtype=D.V := by
  change (⁅pCore 2 (NormalBranch.K D g.val),(⊤:Subgroup (NormalBranch.K D g.val))⁆).map _=_
  rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
  change ⁅(NormalBranch.K D g.val).pCoreIn 2,NormalBranch.K D g.val⁆=D.V
  rw [hS,hc]

theorem core_eq_module_sup_centralizer (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L)
    (hB : ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hc : ⁅D.V,NormalBranch.K D g.val⁆=D.V) :
    D.LT.pCoreIn 2=D.V⊔((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)) := by
  let Q := D.LT.pCoreIn 2
  let K := NormalBranch.K D g.val
  have hKQ : K≤normalizer (Q:Set G) := (hK.trans le_sup_left).trans
    (D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.LT (pCore 2 D.LT)))
  have hQK : Q≤normalizer (K:Set G) := SourcePairResidual.twoCore_normalizes_pair h g
  have hVQ : D.V≤Q := by
    change D.V≤D.LT.pCoreIn 2
    simpa only [pCoreIn,map_subgroupOf_eq_of_le h.V_le_LT] using
      map_mono (f := D.LT.subtype) h.reduced.le_pCore
  have hcomm : ⁅K,Q⁆≤K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 D.LT).to_le (le_normalizer_iff_commutator_le_right.mp hKQ))
      (le_normalizer_iff_commutator_le_left.mp hQK) (normalizer_commutator_ge_left _ _)
  have hb := pair_block_layer g hS hc
  have he := hB.two_subgroup_eq_module_sup_centralizer (isPGroup_pCoreIn 2 D.LT)
    hKQ (hb.symm ▸ hVQ) hcomm
  rw [hb] at he
  apply he.trans
  congr 1
  apply le_antisymm
  · exact inf_le_inf (h.sylow_centralizer.symm.le.trans inf_le_left) le_rfl
  · intro t ht
    refine ⟨h.sylow_centralizer.le ⟨ht.1,?_⟩,ht.2⟩
    exact centralizer_le (hS ▸ pCoreIn_le 2 K) ht.2

include d in
theorem module_inf_pair_centralizer (h : D.Hypothesis) (g : D.L)
    (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hc : ⁅D.V,NormalBranch.K D g.val⁆=D.V) :
    D.V⊓centralizer (NormalBranch.K D g.val:Set G)=⊥ := by
  have hn : NormalBranch.K D g.val≤normalizer
      (D.V⊓centralizer (NormalBranch.K D g.val:Set G):Set G) :=
    (le_inf (hK.trans (le_sup_left.trans d.normalizes_V))
      ((NormalBranch.K D g.val).le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  rcases SourceFiveSpan.invariant_subgroup d hK a hi _ inf_le_left hn with hz|he
  · exact hz
  · have hh : D.V≤centralizer (NormalBranch.K D g.val:Set G) := he.symm.le.trans inf_le_right
    have hv : D.V=⊥ := hc.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hh)
    have hp : D.V₁=⊥ := le_bot_iff.mp ((h.point_lt.le.trans h.plus_le).trans_eq hv)
    have hh := h.point_card
    rw [hp,card_bot] at hh
    contradiction

include d in
theorem exists_original_split_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) :
    ChapterC.IsAlternatingBlock D.L 6 ∧ ∃g:D.L,g.val∉D.Gz ∧
      NormalBranch.K D g.val≤D.L ∧ D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      D.LT.pCoreIn 2=D.V⊔((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)) ∧
      D.V⊓centralizer (NormalBranch.K D g.val:Set G)=⊥ := by
  obtain ⟨a,g,hg,_,hK,hL,hp,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  exact ⟨(SourceSixBlock.source13_5_15_four d h e hseed hn hU).1,g,hg,hK,hL,hB,
    core_eq_module_sup_centralizer h g hK hB hS hc,
    module_inf_pair_centralizer d h g hK a hi hc⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreSplit
end
