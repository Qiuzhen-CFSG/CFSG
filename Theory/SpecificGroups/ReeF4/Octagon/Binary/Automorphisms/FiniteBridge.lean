module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Lines
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Checks
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The certified finite binary Ree graph is the literal coset building

The existing Parrott point certificate gives inverse-representative coordinates
on the 1755 first-parabolic cosets. A checked signed-generator tree carries the
base line triple through all 2925 second-parabolic cosets; the checked row keys
and actual parabolic index make these line coordinates bijective. Combining
the two coordinate maps gives the graph isomorphism with exact incidence,
vertex types, and base vertices.

All finite certificates are discharged here. This identifies the concrete
graph used in Aschbacher–Smith J.5.6–J.5.7, printed pp.447–448; the separate
identification of its full automorphism group is not an input to this bridge.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry

def lineEquiv : Fin 2925 ≃ LineCoset := lineEquivOfValid LineData.valid

theorem lineEquiv_incidence (p : Fin 1755) (l : Fin 2925) :
    pointOnLine (pointEquiv p) (lineEquiv l) ↔
      p.val ∈ FiniteGraph.adjacency (1755+l.val) :=
  lineMapOfValid_incidence LineData.valid l p

theorem lineEquiv_zero : lineEquiv 0 = ((1 : Model 0) : LineCoset) :=
  lineEquivOfValid_zero LineData.valid

def typedEquiv : PointCoset ⊕ LineCoset ≃ CosetGeometry.Vertex family where
  toFun := Sum.elim pointVertex lineVertex
  invFun := fun v => match v with
    | ⟨false,p⟩ => Sum.inl p
    | ⟨true,l⟩ => Sum.inr l
  left_inv x := by cases x <;> rfl
  right_inv v := by rcases v with ⟨b,q⟩; cases b <;> rfl

def vertexEquiv : FiniteGraph.Vertex ≃ CosetGeometry.Vertex family :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr pointEquiv lineEquiv).trans typedEquiv)

theorem vertexEquiv_point (p : Fin 1755) :
    vertexEquiv (FiniteGraph.point p) = pointVertex (pointEquiv p) := by
  change typedEquiv ((Equiv.sumCongr pointEquiv lineEquiv)
    (finSumFinEquiv.symm (Fin.castAdd 2925 p))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem vertexEquiv_line (l : Fin 2925) :
    vertexEquiv (FiniteGraph.line l) = lineVertex (lineEquiv l) := by
  change typedEquiv ((Equiv.sumCongr pointEquiv lineEquiv)
    (finSumFinEquiv.symm (Fin.natAdd 1755 l))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem vertex_cases (i : FiniteGraph.Vertex) :
    (∃p, i=FiniteGraph.point p) ∨ (∃l, i=FiniteGraph.line l) := by
  obtain ⟨s,rfl⟩ := (finSumFinEquiv : Fin 1755 ⊕ Fin 2925 ≃ FiniteGraph.Vertex).surjective i
  cases s with
  | inl p => exact Or.inl ⟨p,rfl⟩
  | inr l => exact Or.inr ⟨l,rfl⟩

private theorem pointVertex_not_adj (p q : PointCoset) :
    ¬ (graph family).Adj (pointVertex p) (pointVertex q) := by
  intro h
  exact h.1 rfl

private theorem lineVertex_not_adj (l m : LineCoset) :
    ¬ (graph family).Adj (lineVertex l) (lineVertex m) := by
  intro h
  exact h.1 rfl

theorem vertexEquiv_adj (i j : FiniteGraph.Vertex) :
    (graph family).Adj (vertexEquiv i) (vertexEquiv j) ↔ FiniteGraph.graph.Adj i j := by
  rcases vertex_cases i with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;>
    rcases vertex_cases j with ⟨q,rfl⟩ | ⟨m,rfl⟩
  · rw [vertexEquiv_point,vertexEquiv_point]
    exact iff_of_false (pointVertex_not_adj _ _) (FiniteGraph.point_point_not_adj p q)
  · rw [vertexEquiv_point,vertexEquiv_line,FiniteGraph.point_line_adj_iff]
    exact lineEquiv_incidence p m
  · rw [vertexEquiv_line,vertexEquiv_point,
      (graph family).adj_comm (lineVertex (lineEquiv l)) (pointVertex (pointEquiv q)),
      FiniteGraph.graph.adj_comm (FiniteGraph.line l) (FiniteGraph.point q),
      FiniteGraph.point_line_adj_iff]
    exact lineEquiv_incidence q l
  · rw [vertexEquiv_line,vertexEquiv_line]
    exact iff_of_false (lineVertex_not_adj _ _) (FiniteGraph.line_line_not_adj l m)

/-- The finite 4680-vertex graph is the literal binary Ree incidence graph. -/
def graphIso : FiniteGraph.graph ≃g graph family where
  toEquiv := vertexEquiv
  map_rel_iff' := vertexEquiv_adj _ _

theorem graphIso_point (p : Fin 1755) :
    graphIso (FiniteGraph.point p) = pointVertex (pointEquiv p) := vertexEquiv_point p

theorem graphIso_line (l : Fin 2925) :
    graphIso (FiniteGraph.line l) = lineVertex (lineEquiv l) := vertexEquiv_line l

theorem graphIso_type (i : FiniteGraph.Vertex) :
    (graphIso i).type = decide (1755 ≤ i.val) := by
  rcases vertex_cases i with ⟨p,rfl⟩ | ⟨l,rfl⟩
  · rw [graphIso_point]
    change false = decide (1755 ≤ p.val)
    simp only [show ¬1755 ≤ p.val from by omega, decide_false]
  · rw [graphIso_line]
    change true = decide (1755 ≤ 1755+l.val)
    simp only [Nat.le_add_right, decide_true]

theorem graphIso_base_point :
    graphIso (FiniteGraph.point 0) = CosetGeometry.base family false := by
  rw [graphIso_point,pointEquiv_zero]
  rfl

theorem graphIso_base_line :
    graphIso (FiniteGraph.line 0) = CosetGeometry.base family true := by
  rw [graphIso_line,lineEquiv_zero]
  rfl

theorem graphIso_neighbor_iff (i j : FiniteGraph.Vertex) :
    graphIso j ∈ (graph family).neighborSet (graphIso i) ↔
      j ∈ FiniteGraph.graph.neighborSet i := vertexEquiv_adj i j

end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
