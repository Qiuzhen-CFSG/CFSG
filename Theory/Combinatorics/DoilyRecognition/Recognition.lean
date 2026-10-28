module

public import Theory.Combinatorics.DoilyRecognition.Duads
public import Theory.Combinatorics.DuadGraph.Defs

/-!
# Recognition of the (15,6,1,3) graph

The original graph is identified, on its original vertex carrier, with the
disjoint-duad graph KG(6,2). The proof uses the triangle matching frame and
its parity normalization; no recognition certificate is an input.

Source: Aschbacher, Sporadic Groups (1994), p249, Exercise2(3), used in the
U₄(3) recognition following §45.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily
variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable {G:SimpleGraph Ω} [DecidableRel G.Adj]

omit [Fintype Ω] [DecidableEq Ω] [DecidableRel G.Adj] in
noncomputable def NormalFrame.iso (F:NormalFrame G) : G ≃g DuadGraph.graph where
  toEquiv := F.vertex.symm.trans (duadEquiv F.sign)
  map_rel_iff' := by
    intro x y
    change Disjoint (duadTable F.sign (F.vertex.symm x))
      (duadTable F.sign (F.vertex.symm y)) ↔ G.Adj x y
    rw [duadTable_adj,← F.adj_iff]
    simp

 theorem isomorphic_duadGraph (h:G.IsSRGWith 15 6 1 3) :
    Nonempty (G ≃g DuadGraph.graph) := by
  obtain ⟨F⟩:=exists_normalFrame h
  exact ⟨F.iso⟩

 theorem isomorphic_duadGraph_of_parameters
    (hcard:Fintype.card Ω=15) (hdeg:∀x,G.degree x=6)
    (hadj:∀x y,G.Adj x y→Fintype.card (G.commonNeighbors x y)=1)
    (hnon:∀x y,x≠y→¬G.Adj x y→Fintype.card (G.commonNeighbors x y)=3) :
    Nonempty (G ≃g DuadGraph.graph) := by
  apply isomorphic_duadGraph
  exact ⟨hcard,hdeg,hadj,fun{v w}=>hnon v w⟩
end Theory.Combinatorics.Doily
