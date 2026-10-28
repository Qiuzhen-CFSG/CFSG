module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSource
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalIndex
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalCoreIntersection

/-!
# The exceptional centralizer component in the original normal branch

For the actual collapsed A₅ pair from 13.5.14, the order-two alternative for
C_T(K) places K in the local component family of C_G(C_T(K)). The proved
index-two source theorem supplies its containing C-component K_D. The original
normal pair then shows V ∩ O₂(K_D C_T(K)) = 1.

The final theorem constructs this component directly from the original setup;
no component or normalizer witness is an additional input. This is the middle
paragraph of Aschbacher--Smith 13.5.15, printed p.920, before the definition of T₁.
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalComponent
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem exceptional_component_exists (g:D.L) (hK:NormalBranch.K D g.val≤D.L)
    (hL:D.L₁≤NormalBranch.K D g.val) (hp:IsPPerfect 2 (NormalBranch.K D g.val))
    (a:alternatingGroup (Fin 6))
    (hi:((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS:(NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hcard:Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=2) :
    let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
    ∃KD:Subgroup G, NormalBranch.K D g.val≤KD ∧ KD≤centralizer (C:Set G) ∧
      (KD.subgroupOf (centralizer (C:Set G))).IsCComponent ∧
      D.V⊓(KD⊔C).pCoreIn 2=⊥ := by
  let K:=NormalBranch.K D g.val
  let C:=(D.T:Subgroup G)⊓centralizer (K:Set G)
  let J:=centralizer (C:Set G)
  let T₀:=(D.T:Subgroup G)⊓J
  have hB:=SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc:=SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit:=SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hCL:=SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU
  have hlocal:=SourceExceptionalSylow.exceptional_pair_mem_centralizer_local_family
    d h e hseed hn hU g hK a hi hS hp hsplit hCL hcard
  obtain ⟨S,hTS,hindex⟩:=SourceExceptionalIndex.exists_exceptional_centralizer_sylow
    d h e hseed hn hU g hK hp a hi hcard
  have hQ:=SourceExceptionalCoreIntersection.exceptional_centralizer_sqtk_quotient d g hcard
  obtain ⟨B,hB,hu⟩:=Chapter1.Section02.index_le_two_local_component_source hQ S hTS hindex hlocal
  let KD:=B.map J.subtype
  have hKD:KD≤J:=map_subtype_le _
  have hKJ:K≤J:=le_centralizer_iff.mp inf_le_right
  have hKKD:K≤KD:=by
    have hm:=map_mono (f:=J.subtype) hB.2
    change (K.subgroupOf J).map J.subtype≤KD at hm
    rwa [map_subgroupOf_eq_of_le hKJ] at hm
  have hcomp:(KD.subgroupOf J).IsCComponent:=by
    have hb:KD.subgroupOf J=B:=comap_map_eq_self_of_injective J.subtype_injective B
    rw [hb]
    exact hB.1
  obtain ⟨r,hrH,hr,hrR,hcore,hIn,hRJ,hRKD,hdis⟩:=
    SourceExceptionalCoreIntersection.exists_original_core_disjoint
      d h e hseed hn hU g hK hL a hi KD hKKD hKD hcomp hcard
  exact ⟨KD,hKKD,hKD,hcomp,hdis⟩

theorem exists_original_exceptional_component :
    ∃g:D.L,g.val∉D.Gz ∧ NormalBranch.K D g.val≤D.L ∧
      D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      (NormalBranch.K D g.val).pCoreIn 2=D.V ∧
      let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
      D.LT.pCoreIn 2=D.V⊔C ∧
      (D.LT.pCoreIn 2=D.V ∨ Nat.card C=2 ∧
        ∃KD:Subgroup G, NormalBranch.K D g.val≤KD ∧ KD≤centralizer (C:Set G) ∧
          (KD.subgroupOf (centralizer (C:Set G))).IsCComponent ∧
          D.V⊓(KD⊔C).pCoreIn 2=⊥) := by
  obtain ⟨a,g,hg,_,hK,hL,hp,_,_,hi,hS⟩:=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hB:=SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc:=SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit:=SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
  have hcard:Nat.card C≤2:=
    SourcePairCentralizerBound.pair_centralizer_card_le_two_source d h e hseed hn hU g hK a hi hS
  refine ⟨g,hg,hK,hL,hB,hS,hsplit,?_⟩
  have hpos:0<Nat.card C:=Nat.card_pos
  rcases (show Nat.card C=1 ∨ Nat.card C=2 by omega) with h1|h2
  · left
    have hz:C=⊥:=card_eq_one.mp h1
    simpa only [show ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=⊥ from hz,
      sup_bot_eq] using hsplit
  · exact Or.inr ⟨h2,exceptional_component_exists d h e hseed hn hU g hK hL hp a hi hS h2⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalComponent
end
