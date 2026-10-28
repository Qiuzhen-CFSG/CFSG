module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Incidence

/-!
# The common-neighbor count forced by 47.5–47.6

The PDF of Aschbacher, *Sporadic Groups* (1994), p.264, prints 18 in
47.6(3). This is inconsistent with 47.5 and the preceding two clauses.
The 36 neighbors of X partition into Y, common neighbors of X and Y,
15 vertices generating SL₂(3) with Y, and 12 generating A₅ with Y.
The actual group orders 3, 12, 24 and 60 separate these cases, so the
common-neighbor count is 8. This also agrees with the double count in 47.7.

The theorem below proves that implication from the earlier exact
hypotheses; it does not assert that the suborbit inputs follow from Seed.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

theorem common_neighbors_card (D : Seed G) (hcover : FourJoinTypes D)
    {A B : D.Vertex} (hab : D.graph.Adj A B)
    (hdegree : {U | D.graph.Adj A U}.ncard = 36)
    (hsl : {U | D.graph.Adj A U ∧ sl2Join D B U}.ncard = 15)
    (ha5 : {U | D.graph.Adj A U ∧ a5Join D B U}.ncard = 12) :
    {U | D.graph.Adj A U ∧ D.graph.Adj B U}.ncard = 8 := by
  let C : Set D.Vertex := {U | D.graph.Adj A U ∧ D.graph.Adj B U}
  let S : Set D.Vertex := {U | D.graph.Adj A U ∧ sl2Join D B U}
  let T : Set D.Vertex := {U | D.graph.Adj A U ∧ a5Join D B U}
  have hcs : Disjoint C S := Set.disjoint_left.mpr fun U hc hs => by
    have := card_join_of_adj D hc.2
    have := card_join_of_sl2Join D hs.2
    omega
  have hct : Disjoint C T := Set.disjoint_left.mpr fun U hc ht => by
    have := card_join_of_adj D hc.2
    have := card_join_of_a5Join D ht.2
    omega
  have hst : Disjoint S T := Set.disjoint_left.mpr fun U hs ht => by
    have := card_join_of_sl2Join D hs.2
    have := card_join_of_a5Join D ht.2
    omega
  have hb : B ∉ C ∪ S ∪ T := by
    rintro ((hc | hs) | ht)
    · exact hc.2.ne rfl
    · have hh := card_join_of_sl2Join D hs.2
      rw [sup_idem, D.vertex_card] at hh
      omega
    · have hh := card_join_of_a5Join D ht.2
      rw [sup_idem, D.vertex_card] at hh
      omega
  have he : {U | D.graph.Adj A U} = insert B (C ∪ S ∪ T) := by
    ext U
    constructor
    · intro hU
      rcases hcover B U with he | hc | hs | ht
      · exact Or.inl he.symm
      · exact Or.inr (Or.inl (Or.inl ⟨hU, hc⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hU, hs⟩))
      · exact Or.inr (Or.inr ⟨hU, ht⟩)
    · rintro (rfl | ((hc | hs) | ht))
      · exact hab
      · exact hc.1
      · exact hs.1
      · exact ht.1
  rw [he, Set.ncard_insert_of_notMem hb,
    Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hct, hst⟩),
    Set.ncard_union_eq hcs] at hdegree
  change C.ncard = 8
  change S.ncard = 15 at hsl
  change T.ncard = 12 at ha5
  omega

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
