module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.CommonNeighbors

/-!
# The two mixed975-point sets

The original strongly regular graph has1755 neighbors at every point and780
common neighbors at a nonadjacent pair. Removing their intersection gives the
literal mixed sets of975 points in both orientations. The nonneighbor set Sigma
uses the same original q and coset action throughout.

Source: Aschbacher–Smith J.5.5(4), printed p.446.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F)

/-- The literal nonneighbor set at a source vertex. -/
def sourceSigma (x:Cosets F) : Set (Cosets F) :=
  {y | y≠x ∧ ¬(sourceGraph F q hq hs).Adj x y}

omit [Finite G] in
theorem sourceSigma_smul (a:G) (x y:Cosets F) :
    a•y∈sourceSigma F q hq hs (a•x) ↔ y∈sourceSigma F q hq hs x := by
  change (a•y≠a•x ∧ ¬(sourceGraph F q hq hs).Adj (a•x) (a•y))↔_
  rw [sourceGraph_adj_smul]
  exact and_congr (not_congr (MulAction.injective a).eq_iff) Iff.rfl

omit [Finite G] in
theorem RudvalisAction.sigma_base {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    sourceSigma F q hq hs (basePoint F)=orbit F (g•basePoint F) := by
  rw [h.partition,←sourceGraph_neighbor_base F q hq hs]
  ext x
  change (x≠basePoint F ∧ ¬(sourceGraph F q hq hs).Adj (basePoint F) x) ↔
    ¬(x=basePoint F ∨ (sourceGraph F q hq hs).Adj (basePoint F) x)
  exact not_or.symm

omit [Finite G] in
theorem RudvalisAction.second_mem_sigma {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    g•basePoint F∈sourceSigma F q hq hs (basePoint F) :=
  (h.sigma_base F q hq hs).symm ▸ mem_orbit_self _

theorem RudvalisAction.mixed_neighbors_card {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    Nat.card ((sourceGraph F q hq hs).neighborSet (basePoint F) ∩
      sourceSigma F q hq hs (g•basePoint F) : Set (Cosets F))=975 := by
  let Γ:=sourceGraph F q hq hs
  have he : Γ.neighborSet (basePoint F)∩sourceSigma F q hq hs (g•basePoint F)=
      Γ.neighborSet (basePoint F)\Γ.neighborSet (g•basePoint F) := by
    ext x
    constructor
    · rintro ⟨hx,hne,hn⟩; exact ⟨hx,hn⟩
    · rintro ⟨hx,hn⟩
      refine ⟨hx,?_,hn⟩
      rintro rfl
      exact (h.second_mem_sigma F q hq hs).2 hx
  have hc:=Set.ncard_union_eq (Set.disjoint_sdiff_inter :
    Disjoint (Γ.neighborSet (basePoint F)\Γ.neighborSet (g•basePoint F))
      (Γ.neighborSet (basePoint F)∩Γ.neighborSet (g•basePoint F)))
  rw [Set.sdiff_union_inter] at hc
  symm at hc
  have hk:Nat.card ↥(Γ.neighborSet (basePoint F))=1755:=
    (Nat.card_congr (Equiv.setCongr (sourceGraph_neighbor_base F q hq hs))).trans h.first_length
  have hm:Nat.card ↥(Γ.neighborSet (basePoint F)∩Γ.neighborSet (g•basePoint F))=780:=
    (h.parameters F q hq hs).2
  change Nat.card ↥(Γ.neighborSet (basePoint F)\Γ.neighborSet (g•basePoint F))+
    Nat.card ↥(Γ.neighborSet (basePoint F)∩Γ.neighborSet (g•basePoint F))=
      Nat.card ↥(Γ.neighborSet (basePoint F)) at hc
  rw [hm,hk] at hc
  have hd:Nat.card ↥(Γ.neighborSet (basePoint F)\Γ.neighborSet (g•basePoint F))=975:=by omega
  exact (Nat.card_congr (Equiv.setCongr he)).trans hd

attribute [local instance] Classical.propDecidable

theorem RudvalisAction.reverse_mixed_neighbors_card {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    Nat.card ((sourceGraph F q hq hs).neighborSet (g•basePoint F) ∩
      sourceSigma F q hq hs (basePoint F) : Set (Cosets F))=975 := by
  let Γ:=sourceGraph F q hq hs
  have he : Γ.neighborSet (g•basePoint F)∩sourceSigma F q hq hs (basePoint F)=
      Γ.neighborSet (g•basePoint F)\Γ.neighborSet (basePoint F) := by
    ext x
    constructor
    · rintro ⟨hx,hne,hn⟩; exact ⟨hx,hn⟩
    · rintro ⟨hx,hn⟩
      refine ⟨hx,?_,hn⟩
      rintro rfl
      exact (h.second_mem_sigma F q hq hs).2 hx.symm
  let : Fintype (Cosets F):=Fintype.ofFinite _
  have hk:Nat.card ↥(Γ.neighborSet (g•basePoint F))=1755:=by
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
    exact (h.source_srg F q hq hs).regular _
  have hc:=Set.ncard_union_eq (Set.disjoint_sdiff_inter :
    Disjoint (Γ.neighborSet (g•basePoint F)\Γ.neighborSet (basePoint F))
      (Γ.neighborSet (g•basePoint F)∩Γ.neighborSet (basePoint F)))
  rw [Set.sdiff_union_inter] at hc
  symm at hc
  have hm:Nat.card ↥(Γ.neighborSet (g•basePoint F)∩Γ.neighborSet (basePoint F))=780:=by
    rw [Set.inter_comm]; exact (h.parameters F q hq hs).2
  change Nat.card ↥(Γ.neighborSet (g•basePoint F)\Γ.neighborSet (basePoint F))+
    Nat.card ↥(Γ.neighborSet (g•basePoint F)∩Γ.neighborSet (basePoint F))=
      Nat.card ↥(Γ.neighborSet (g•basePoint F)) at hc
  rw [hm,hk] at hc
  have hd:Nat.card ↥(Γ.neighborSet (g•basePoint F)\Γ.neighborSet (basePoint F))=975:=by omega
  exact (Nat.card_congr (Equiv.setCongr he)).trans hd

end CFSG.Quasithin.ChapterJ.Section05
