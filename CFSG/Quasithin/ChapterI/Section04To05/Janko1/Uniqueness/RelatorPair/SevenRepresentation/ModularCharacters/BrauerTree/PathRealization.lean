module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Stem

/-!
# Dimension and coordinate assembly for the principal eleven-block path

Once the genuine real stem and its ordinary-row degrees are known, its
character identities at the identity determine the edge dimensions over the
natural numbers. Transporting each actual irreducible along the resulting
dimension equality gives the requested coordinate modules over `ElevenClosure`.

This is conditional assembly, not the source existence theorem. Constructing
the stem (Feit, Chapter VII) and ordering it from the Janko source hypotheses
(Janko, J. Algebra 3 (1966), 147–186; Gorenstein §16.6 p.482) remain separate
mathematical obligations. No model recognition is used.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

/-- The natural incidence equations determine all ten edge dimensions. -/
public theorem degree_eq_pathDegree {a : Fin 10 → ℕ}
    (h : lineIncidence a = orderedVertexDegree) : a = pathDegree := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  have h8 := congrFun h 8
  have h9 := congrFun h 9
  dsimp [lineIncidence, orderedVertexDegree] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  funext i
  fin_cases i <;> dsimp [pathDegree] <;> omega

/-- Application to the actual coordinate modules in a real stem. The row
ordering premise must be discharged from the source hypotheses. -/
public theorem pathModules_of_ordered_realStem {G : Type*} [Group G] [Finite G]
    {d : OrdinaryData G} (s : RealStem G d)
    (horder : (fun i => ordinaryDegree (s.row i)) = orderedVertexDegree) :
    Nonempty (PathModules G) := by
  have hdim : s.degree = pathDegree := degree_eq_pathDegree
    ((funext s.degree_incidence).trans horder)
  have coordinate : ∀ i, ∃ ρ : Representation ElevenClosure G
      (Fin (pathDegree i) → ElevenClosure), Representation.IsIrreducible ρ := by
    intro i
    have hi : s.degree i = pathDegree i := congrFun hdim i
    rw [← hi]
    exact ⟨s.rep i, s.irreducible i⟩
  classical
  exact ⟨⟨fun i => (coordinate i).choose, fun i => (coordinate i).choose_spec⟩⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
