module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.OrbitAdjacency

/-!
# Canonical J.5.13 orbital graph

The base, first building points and normalized second cosets form one explicit
vertex set. Every adjacency case is proved from the original action, native
opposition and the 780/975 orbit producers.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
open ReeF4.Octagon.Binary
attribute [local instance] Automorphisms.FiniteBridge.pointAction
namespace CFSG.Quasithin.ChapterJ.Section05
attribute [local instance] canonicalSecondAction

/-- The canonical relation of J.5.13, on the base, building points and cosets
of the fixed native second stabilizer. Its two cross-orbit tests use the
actual native stabilizers and the original orbit lengths. -/
def canonicalRelation : CanonicalVertex→CanonicalVertex→Prop
  | .inl _,.inl _=>False
  | .inl _,.inr (.inl _)=>True
  | .inl _,.inr (.inr _)=>False
  | .inr (.inl _),.inl _=>True
  | .inr (.inr _),.inl _=>False
  | .inr (.inl p),.inr (.inl r)=>p≠r ∧ pointDistance p r≠8
  | .inr (.inl p),.inr (.inr s)=>Nat.card (orbit (stabilizer (ReeF4.Model 0) s) p)=780
  | .inr (.inr s),.inr (.inl p)=>Nat.card (orbit (stabilizer (ReeF4.Model 0) s) p)=780
  | .inr (.inr s),.inr (.inr t)=>Nat.card (orbit (stabilizer (ReeF4.Model 0) s) t)=975

variable {G:Type*} [Group G] [Finite G]
variable {F:Subgroup G} {q g:G} (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F)
namespace NormalizedCoordinates
variable {h:RudvalisAction F (q•basePoint F) (g•basePoint F)} (c:NormalizedCoordinates h)

theorem vertex_adj_iff (u v:CanonicalVertex) :
    (sourceGraph F q hq hs).Adj (c.vertexEquiv hq u) (c.vertexEquiv hq v) ↔
      canonicalRelation u v := by
  rcases u with u | (u|u) <;> rcases v with v | (v|v)
  · exact iff_false_intro ((sourceGraph F q hq hs).loopless.irrefl _)
  · exact iff_true_intro ((sourceGraph_neighbor_base F q hq hs).ge (c.point.symm v).property)
  · exact iff_false_intro ((h.sigma_base F q hq hs).ge (c.second.symm v).property).2
  · exact iff_true_intro (((sourceGraph_neighbor_base F q hq hs).ge (c.point.symm u).property).symm)
  · simpa only [canonicalRelation,c.vertexEquiv_point,c.point.apply_symm_apply] using
      c.first_adj_iff hq hs (c.point.symm u) (c.point.symm v)
  · change (sourceGraph F q hq hs).Adj (c.point.symm u).val (c.second.symm v).val ↔ _
    rw [SimpleGraph.adj_comm,h.second_first_adj_iff_card F q hq hs,
      c.second_first_orbit_card,c.second.apply_symm_apply,c.point.apply_symm_apply]
    rfl
  · exact iff_false_intro (fun he=>
      ((h.sigma_base F q hq hs).ge (c.second.symm u).property).2 he.symm)
  · change (sourceGraph F q hq hs).Adj (c.second.symm u).val (c.point.symm v).val ↔ _
    rw [h.second_first_adj_iff_card F q hq hs,c.second_first_orbit_card,
      c.second.apply_symm_apply,c.point.apply_symm_apply]
    rfl
  · change (sourceGraph F q hq hs).Adj (c.second.symm u).val (c.second.symm v).val ↔ _
    rw [h.second_second_adj_iff_card F q hq hs,c.second_second_orbit_card,
      c.second.apply_symm_apply,c.second.apply_symm_apply]
    rfl
end NormalizedCoordinates

namespace RudvalisAction
variable (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
variable {H:Type*} [Group H] [Finite H] {E:Subgroup H} {r k:H}
    (hr:r∉E) (ht:r•(r•basePoint E)=basePoint E)
    (j:RudvalisAction E (r•basePoint E) (k•basePoint E))
include h j

/-- J.5.13: the original rank-three orbital graph is independent of the source
group. The common relation is constructed from the actual native local actions. -/
theorem source_graph_isomorphic :
    Nonempty (sourceGraph F q hq hs ≃g sourceGraph E r hr ht) := by
  obtain ⟨c⟩:=RudvalisAction.exists_normalizedCoordinates h
  obtain ⟨d⟩:=RudvalisAction.exists_normalizedCoordinates j
  refine ⟨{
    toEquiv := (c.vertexEquiv hq).symm.trans (d.vertexEquiv hr)
    map_rel_iff' := ?_ }⟩
  intro u v
  change (sourceGraph E r hr ht).Adj
    (d.vertexEquiv hr ((c.vertexEquiv hq).symm u))
    (d.vertexEquiv hr ((c.vertexEquiv hq).symm v)) ↔ _
  rw [d.vertex_adj_iff hr ht,←c.vertex_adj_iff hq hs,
    (c.vertexEquiv hq).apply_symm_apply,(c.vertexEquiv hq).apply_symm_apply]
end RudvalisAction
end CFSG.Quasithin.ChapterJ.Section05
