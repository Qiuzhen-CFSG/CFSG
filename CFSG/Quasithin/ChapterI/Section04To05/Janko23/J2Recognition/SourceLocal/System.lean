module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Applications
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry

/-!
# The source J₂ uniqueness system

For a simple source group, the involution and prime-local calculations give
the four suborbits and the A₅ pointwise edge fixer. Choose a neighbor and a
dihedral ten in that fixer. Its full centralizer is the local A₅. The proved
proper-overgroup and finite A₅ calculations discharge all three generation
identities, constructing condition (U) from the original seed alone.

This supplies the source system in Aschbacher, *Sporadic Groups* (1994),
47.10, pp.266–267. Local comparison and the ambient triangle arguments remain
separate: neither is an input hidden in the constructed system.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- A neighbor exists because its source suborbit has cardinality 36. -/
theorem exists_neighbor (D : Seed G) : ∃ Y : D.Vertex, D.graph.Adj D.base Y := by
  have hc := (InvolutionGeometry.Applications.fourSuborbits D).neighbor_card
  obtain ⟨Y, hY⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  exact ⟨Y, hY⟩

/-- The dihedral subgroup is chosen inside the literal pointwise edge fixer. -/
noncomputable def sourceFrame (D : Seed G) : EdgeFrame D :=
  edgeFrameOfAlternatingFixer D (exists_neighbor D).choose
    (exists_neighbor D).choose_spec
    (InvolutionGeometry.Applications.edgeFixer_equiv D
      (exists_neighbor D).choose_spec).some

namespace EdgeFrame
variable {D : Seed G} (F : EdgeFrame D)

/-- The actual local centralizer has the source A₅ model. -/
noncomputable def localEquiv : F.K ≃* alternatingGroup (Fin 5) :=
  (InvolutionGeometry.Applications.edgeFrame_calculations D F).1.some

/-- All source generation inputs are discharged for any actual edge frame. -/
noncomputable def localData : LocalData D := by
  have he := InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent
  have h := F.local_calculations he F.localEquiv
  exact localDataOfCalculations (InvolutionGeometry.Applications.fourSuborbits D) F
    (InvolutionGeometry.Applications.edgeFrame_calculations D F).2.2 h.1 h.2.1 h.2.2

@[simp] theorem localData_y : F.localData.y = F.y := rfl

@[simp] theorem localData_K : F.localData.K = F.K := rfl

/-- Both endpoints retain their literal embeddings in C_G(B). -/
theorem localData_endpoints : D.X ⊔ F.localData.y.val ≤ F.localData.K :=
  F.endpoints_le (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent)

/-- The local orbit graph is the induced subgroup graph inside C_G(B). -/
theorem localData_localEdge_iff (A B : D.Vertex) :
    F.localData.simpleSystem.localEdge A B ↔
      D.graph.Adj A B ∧ A.val ≤ F.K ∧ B.val ≤ F.K :=
  F.localData.localEdge_iff_of_alternatingFive F.localEquiv
    (le_sup_left.trans F.localData_endpoints)
    (le_sup_right.trans F.localData_endpoints) D.faithful A B

end EdgeFrame

/-- Condition (U) on the literal source subgroup graph, without local premises. -/
noncomputable def sourceSystem (D : Seed G) : System G D.Vertex :=
  (sourceFrame D).localData.simpleSystem

/-- Original source type supplies a seed and its full uniqueness system. -/
theorem exists_source_system (h : J2Type G) :
    ∃ D : Seed G, Nonempty (System G D.Vertex) := by
  obtain ⟨D⟩ := exists_seed h
  exact ⟨D, ⟨sourceSystem D⟩⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
