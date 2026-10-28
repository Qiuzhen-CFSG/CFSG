module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSylow
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer.GeneratedCore

/-!
# The original exceptional local component of 13.5.15

Select K from the original normal A₆ hypotheses. The direct generated-core
proof gives C_T(L)=1, so the normalized-cocycle theorem reduces C_T(K)
to order one or two. In the first case Q=V. In the second, the original
pair is a member of L(C_G(C_T(K)),C_T(C_T(K))): normalization follows
from its maximal A₅ image and two-residual, and the actual U_H image
supplies the Sylow condition.

This discharges the local-family premise of the source 1.2.5 application
in Aschbacher–Smith13.5.15(7), printed p.920, without a maximality,
normalizer, Sylow, or representation hypothesis added to the source.
The index bound and subsequent containing-component construction remain
the next source steps; this theorem does not eliminate the order-two case.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSource
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

/-- The original source either has Q=V or constructs the literal local
component in the exceptional involution centralizer, with no additional
Sylow, normalization, or maximality hypothesis. -/
theorem exists_original_exceptional_pair :
    ∃g:D.L,g.val∉D.Gz ∧ NormalBranch.K D g.val≤D.L ∧
      D.L₁≤NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      (NormalBranch.K D g.val).pCoreIn 2=D.V ∧
      let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
      let T₀:=(D.T:Subgroup G)⊓centralizer (C:Set G)
      D.LT.pCoreIn 2=D.V⊔C ∧
      (D.LT.pCoreIn 2=D.V ∨ Nat.card C=2 ∧
        (NormalBranch.K D g.val).subgroupOf (centralizer (C:Set G))∈
          Chapter1.L (centralizer (C:Set G)) (T₀.subgroupOf (centralizer (C:Set G)))) := by
  obtain ⟨a,g,hg,_,hK,hL,hp,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have hc := SourceFiveSpan.module_commutator d hK a hi h hL hseed
  have hsplit := SourceCoreSplit.core_eq_module_sup_centralizer h g hK hB hS hc
  have hCL := SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core d h e hseed hn hU
  let C:=(D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)
  have hcard : Nat.card C≤2 :=
    SourcePairCentralizerBound.pair_centralizer_card_le_two_source d h e hseed hn hU g hK a hi hS
  refine ⟨g,hg,hK,hL,hB,hS,hsplit,?_⟩
  have hpos : 0<Nat.card C := Nat.card_pos
  rcases (show Nat.card C=1 ∨ Nat.card C=2 by omega) with h1|h2
  · left
    have hC : C=⊥ := card_eq_one.mp h1
    simpa only [show ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=⊥ from hC,
      sup_bot_eq] using hsplit
  · exact Or.inr ⟨h2,SourceExceptionalSylow.exceptional_pair_mem_centralizer_local_family
      d h e hseed hn hU g hK a hi hS hp hsplit hCL h2⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSource
end

