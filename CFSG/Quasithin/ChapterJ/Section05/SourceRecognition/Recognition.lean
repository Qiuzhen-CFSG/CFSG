module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.Canonical
public import Theory.Combinatorics.SimpleGraph.FullActionEquiv

/-!
# Rank-three source recognition

The canonical orbital relation gives an equivariant graph isomorphism between
genuine source actions. The audited full source-graph automorphism theorem
then transfers the original group actions, without an order or catalogue
premise.
-/

@[expose] public section
noncomputable section
open MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G H:Type*} [Group G] [Finite G] [Group H] [Finite H]
variable {F:Subgroup G} {q g:G} (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F)
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
variable {E:Subgroup H} {r k:H} (hr:r∉E) (ht:r•(r•basePoint E)=basePoint E)
    (j:RudvalisAction E (r•basePoint E) (k•basePoint E))
include h j hq hs hr ht

/-- The source recognition preserves the complete original permutation actions,
not only the abstract group orders or local isomorphism types. -/
theorem source_action_equivalent :
    ∃a:sourceGraph F q hq hs ≃g sourceGraph E r hr ht,
      ∃f:G≃*H,∀u x,a (u•x)=f u•a x := by
  let :=h.faithful
  let :=j.faithful
  obtain ⟨a⟩:=h.source_graph_isomorphic hq hs hr ht j
  obtain ⟨f,hf⟩:=SimpleGraph.exists_equivariant_groupEquiv
    (sourceGraph_adj_smul F q hq hs) (sourceGraph_adj_smul E r hr ht)
    (fun b=>(h.source_graph_automorphism_eq_unique_left_action F q hq hs b).exists)
    (fun b=>(j.source_graph_automorphism_eq_unique_left_action E r hr ht b).exists) a
  exact ⟨a,f,hf⟩

/-- J.5.14: any two genuine Rudvalis rank-three actions determine isomorphic
original groups. The concrete Rudvalis action supplies the comparison carrier. -/
theorem source_group_equivalent : Nonempty (G≃*H) := by
  obtain ⟨_,f,_⟩:=h.source_action_equivalent hq hs hr ht j
  exact ⟨f⟩
end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
