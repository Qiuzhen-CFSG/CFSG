module

public import Theory.Combinatorics.DoilyRecognition.Recognition
public import Theory.Combinatorics.DuadGraph.Automorphisms
public import Theory.Combinatorics.GraphAutomorphismTransport
/-!
# Faithful six-letter actions from the original fifteen-vertex graph

The exact (15,6,1,3) parameters construct the duad marking. Conjugating the
original automorphisms through that marking and permuting its six point
stars gives an injective homomorphism into S₆. The marked action theorem
retains point-duad incidence with the original vertex action.

This discharges the graph-recognition step in Aschbacher (1994), p249,
Exercise2(3), without an assumed recognition certificate or extra group model.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily
variable {Ω:Type*} {G:SimpleGraph Ω}

/-- The six-letter action transported through the actual duad marking. -/
noncomputable def sixAction (e:G≃gDuadGraph.graph) : (G≃gG)→*Equiv.Perm (Fin 6) :=
  DuadGraph.pointAction.comp (graphAutomorphismEquiv e).toMonoidHom

theorem sixAction_injective (e:G≃gDuadGraph.graph) : Function.Injective (sixAction e) :=
  DuadGraph.pointAction_injective.comp (graphAutomorphismEquiv e).injective

variable [Fintype Ω] [DecidableEq Ω] [DecidableRel G.Adj]
 theorem automorphisms_embed_six (h:G.IsSRGWith 15 6 1 3) :
    ∃ρ:(G≃gG)→*Equiv.Perm (Fin 6),Function.Injective ρ := by
  obtain ⟨e⟩:=isomorphic_duadGraph h
  exact ⟨sixAction e,sixAction_injective e⟩

 theorem automorphisms_embed_six_of_parameters
    (hcard:Fintype.card Ω=15) (hdeg:∀x,G.degree x=6)
    (hadj:∀x y,G.Adj x y→Fintype.card (G.commonNeighbors x y)=1)
    (hnon:∀x y,x≠y→¬G.Adj x y→Fintype.card (G.commonNeighbors x y)=3) :
    ∃ρ:(G≃gG)→*Equiv.Perm (Fin 6),Function.Injective ρ := by
  obtain ⟨e⟩:=isomorphic_duadGraph_of_parameters hcard hdeg hadj hnon
  exact ⟨sixAction e,sixAction_injective e⟩

variable {A:Type*} [Group A]
/-- The literal faithful permutation-action consumer of the graph recognition. -/
 theorem faithful_action_six (h:G.IsSRGWith 15 6 1 3)
    (ρ:A→*Equiv.Perm Ω) (hf:Function.Injective ρ)
    (hρ:∀a x y,G.Adj (ρ a x) (ρ a y) ↔ G.Adj x y) :
    ∃φ:A→*Equiv.Perm (Fin 6),Function.Injective φ := by
  obtain ⟨e⟩:=isomorphic_duadGraph h
  exact ⟨(sixAction e).comp (graphActionHom ρ hρ),
    (sixAction_injective e).comp (graphActionHom_injective ρ hρ hf)⟩

/-- The six-letter action with its literal incidence relation on the original vertices. -/
 theorem faithful_action_six_marked (h:G.IsSRGWith 15 6 1 3)
    (ρ:A→*Equiv.Perm Ω) (hf:Function.Injective ρ)
    (hρ:∀a x y,G.Adj (ρ a x) (ρ a y) ↔ G.Adj x y) :
    ∃(e:G≃gDuadGraph.graph) (φ:A→*Equiv.Perm (Fin 6)),Function.Injective φ ∧
      ∀a x i, φ a i ∈ (e (ρ a x)).val ↔ i ∈ (e x).val := by
  obtain ⟨e⟩:=isomorphic_duadGraph h
  let φ := (sixAction e).comp (graphActionHom ρ hρ)
  refine ⟨e,φ,(sixAction_injective e).comp (graphActionHom_injective ρ hρ hf),?_⟩
  intro a x i
  let g:DuadGraph.Aut:=graphAutomorphismEquiv e (graphActionHom ρ hρ a)
  have he:g (e x)=e (ρ a x):=by simp [g,graphAutomorphismEquiv,graphActionHom]
  have hm:=DuadGraph.pointAction_mem g i (e x)
  change DuadGraph.pointAction g i ∈ (e (ρ a x)).val ↔ i∈(e x).val
  rw [←he]
  exact hm

 theorem faithful_action_six_of_parameters
    (hcard:Fintype.card Ω=15) (hdeg:∀x,G.degree x=6)
    (hadj:∀x y,G.Adj x y→Fintype.card (G.commonNeighbors x y)=1)
    (hnon:∀x y,x≠y→¬G.Adj x y→Fintype.card (G.commonNeighbors x y)=3)
    (ρ:A→*Equiv.Perm Ω) (hf:Function.Injective ρ)
    (hρ:∀a x y,G.Adj (ρ a x) (ρ a y) ↔ G.Adj x y) :
    ∃φ:A→*Equiv.Perm (Fin 6),Function.Injective φ :=
  faithful_action_six ⟨hcard,hdeg,hadj,fun{v w}=>hnon v w⟩ ρ hf hρ
end Theory.Combinatorics.Doily
