module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupAction.TypedCosetGeometry
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-!
# The critical pair in the F.7 coset graph

Vertices are the two types of cosets of LT and H inside G₀=⟨LT,H⟩.
Adjacency is intersection of differently typed cosets. Vertex and edge
groups are their actual stabilizers, embedded in G. The first kernel fixes
the vertex and all its neighbors; critical distance is the least distance
from γ₀ to a vertex whose first kernel does not contain V.

`CriticalPair` retains the chosen geodesic and the element taking the standard
edge to its terminal edge. It contains no rank, offender, transvection or
symmetry conclusions. Endpoint groups are actual conjugates by that element.
Conjugation here is left conjugation; the corresponding source right
conjugator is the inverse.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.7.2–3,
F.9.10–12 and the setup before 13.8.4, printed pp.311, 321–322 and 946–947.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]

abbrev G0 (L T H : Subgroup G) : Subgroup G := (L ⊔ T) ⊔ H

def cosetFamily (L T H : Subgroup G) : Bool → Subgroup (G0 L T H) :=
  fun i => (if i then H else L ⊔ T).subgroupOf (G0 L T H)

abbrev Vertex (L T H : Subgroup G) := CosetGeometry.Vertex (cosetFamily L T H)
abbrev base (L T H : Subgroup G) (i : Bool) : Vertex L T H :=
  CosetGeometry.base (cosetFamily L T H) i

def graph (L T H : Subgroup G) : SimpleGraph (Vertex L T H) where
  Adj v w := v.type ≠ w.type ∧ CosetGeometry.Incident (cosetFamily L T H) v w
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm _⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def vertexGroup (L T H : Subgroup G) (v : Vertex L T H) : Subgroup G :=
  (MulAction.stabilizer (G0 L T H) v).map (G0 L T H).subtype

def edgeGroup (L T H : Subgroup G) (v w : Vertex L T H) : Subgroup G :=
  vertexGroup L T H v ⊓ vertexGroup L T H w

def firstKernel (L T H : Subgroup G) (v : Vertex L T H) : Subgroup G :=
  vertexGroup L T H v ⊓ ⨅ w, ⨅ (_ : (graph L T H).Adj v w), vertexGroup L T H w

noncomputable def criticalDistance (L T H V : Subgroup G) : ℕ :=
  sInf {n | ∃ v : Vertex L T H, (graph L T H).Reachable (base L T H false) v ∧
    (graph L T H).dist (base L T H false) v = n ∧ ¬ V ≤ firstKernel L T H v}

structure CriticalPair (L T H V : Subgroup G) where
  gamma : Vertex L T H
  path : (graph L T H).Walk (base L T H false) gamma
  length_eq : path.length = criticalDistance L T H V
  distance_eq : (graph L T H).dist (base L T H false) gamma = path.length
  critical : ¬ V ≤ firstKernel L T H gamma
  first : path.getVert 1 = base L T H true
  gb : G0 L T H
  gb_zero : gb • base L T H false = path.getVert (path.length - 1)
  gb_one : gb • base L T H true = gamma

namespace CriticalPair
variable {L T H V : Subgroup G} (c : CriticalPair L T H V)
abbrev previous : Vertex L T H := c.path.getVert (c.path.length - 1)
abbrev second : Vertex L T H := c.path.getVert 2
def Ugamma (V₃ : Subgroup G) : Subgroup G :=
  (Source.UH H V₃).map (MulAut.conj (c.gb : G)).toMonoidHom
def Vgamma : Subgroup G :=
  (Source.VH H V).map (MulAut.conj (c.gb : G)).toMonoidHom
def Qgamma : Subgroup G :=
  (Source.QH H).map (MulAut.conj (c.gb : G)).toMonoidHom
def Aone (V₁ : Subgroup G) : Subgroup G :=
  V₁.map (MulAut.conj (c.gb : G)).toMonoidHom
end CriticalPair

theorem vertexGroup_base (L T H : Subgroup G) (i : Bool) :
    vertexGroup L T H (base L T H i) = if i then H else L ⊔ T := by
  rw [vertexGroup, base, CosetGeometry.stabilizer_base]
  apply map_subgroupOf_eq_of_le
  cases i
  · exact le_sup_left
  · exact le_sup_right

theorem vertexGroup_smul (L T H : Subgroup G) (g : G0 L T H) (v : Vertex L T H) :
    vertexGroup L T H (g • v) =
      (vertexGroup L T H v).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [vertexGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj, map_map,
    vertexGroup, map_map]
  rfl

theorem CriticalPair.vertexGroup_gamma {L T H V : Subgroup G}
    (c : CriticalPair L T H V) :
    vertexGroup L T H c.gamma = H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
  rw [← c.gb_one, vertexGroup_smul, vertexGroup_base]
  rfl

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
