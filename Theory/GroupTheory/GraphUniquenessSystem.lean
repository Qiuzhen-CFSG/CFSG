module

public import Theory.Combinatorics.PairGraphTriangleClosure.WalkClosure
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Graph uniqueness systems

A uniqueness system consists of a faithful vertex- and edge-transitive group
of graph automorphisms, a subgroup, and a distinguished edge in its orbit.
The three generation identities are precisely condition (U) of Aschbacher,
*Sporadic Groups*, §37, p.198. Similarities compare the vertex and local groups
and their intersections. Equivalence additionally requires compatibility with
conjugation by an element reversing the distinguished edge (p.199).

The local graph is its actual edge orbit, and the base condition uses normal
closure of its translated closed walks (§33 and p.200). Neither equivalence nor
the base condition is defined by a group-isomorphism conclusion. Left actions
are used throughout, so conjugation is `t * b * t⁻¹`.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

/-- The pointwise stabilizer of the two ends of an edge. -/
def edgeFixer (G : Type u) {V : Type v} [Group G] [MulAction G V]
    (x y : V) : Subgroup G := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y

/-- The setwise stabilizer of an unordered pair, explicitly allowing reversal. -/
def edgeStabilizer (G : Type u) {V : Type v} [Group G] [MulAction G V]
    (x y : V) : Subgroup G where
  carrier := {g | (g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x)}
  one_mem' := Or.inl ⟨one_smul _ _, one_smul _ _⟩
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
      rcases hb with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
      simp only [Set.mem_ofPred_eq, mul_smul, ha, ha', hb, hb'] <;> tauto
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ha, ha'⟩ | ⟨ha, ha'⟩
    · exact Or.inl ⟨by rw [inv_smul_eq_iff, ha], by rw [inv_smul_eq_iff, ha']⟩
    · exact Or.inr ⟨by rw [inv_smul_eq_iff, ha'], by rw [inv_smul_eq_iff, ha]⟩

/-- A source-faithful uniqueness system with a chosen local edge. -/
structure System (G : Type u) (V : Type v) [Group G] [MulAction G V] where
  graph : SimpleGraph V
  H : Subgroup G
  x : V
  y : V
  adjacent : graph.Adj x y
  preserves : ∀ g : G, ∀ {a b}, graph.Adj a b → graph.Adj (g • a) (g • b)
  faithful : ∀ g : G, (∀ a : V, g • a = a) → g = 1
  vertex_transitive : ∀ a : V, ∃ g : G, g • x = a
  edge_transitive : ∀ a b : V, graph.Adj a b →
    ∃ g : G, (g • x = a ∧ g • y = b) ∨ (g • x = b ∧ g • y = a)
  local_orbit : ∃ h : H, (h : G) • x = y
  generate : H ⊔ MulAction.stabilizer G x = ⊤
  vertex_generate : edgeFixer G x y ⊔ (H ⊓ MulAction.stabilizer G x) =
    MulAction.stabilizer G x
  local_generate : (H ⊓ edgeStabilizer G x y) ⊔ (H ⊓ MulAction.stabilizer G x) = H

namespace System
variable (U : System G V)

/-- The vertex stabilizer. -/
abbrev vertexGroup : Subgroup G := MulAction.stabilizer G U.x

/-- The pointwise edge stabilizer. -/
abbrev edgeGroup : Subgroup G := edgeFixer G U.x U.y

/-- The setwise edge stabilizer. -/
abbrev edgeSetGroup : Subgroup G := edgeStabilizer G U.x U.y

/-- The actual edge relation of the local orbit graph. -/
def localEdge (a b : V) : Prop :=
  ∃ h : U.H, ((h : G) • U.x = a ∧ (h : G) • U.y = b) ∨
    ((h : G) • U.x = b ∧ (h : G) • U.y = a)

/-- Every local edge is an ambient edge. -/
theorem localEdge_adj {a b : V} (h : U.localEdge a b) : U.graph.Adj a b := by
  obtain ⟨h, he | he⟩ := h
  · obtain ⟨rfl, rfl⟩ := he
    exact U.preserves h U.adjacent
  · obtain ⟨rfl, rfl⟩ := he
    exact (U.preserves h U.adjacent).symm

/-- The orbit graph, retaining isolated ambient vertices for convenient walk types. -/
def localGraph : SimpleGraph V where
  Adj := U.localEdge
  symm := ⟨by
    rintro a b ⟨h, he | he⟩
    · exact ⟨h, Or.inr he⟩
    · exact ⟨h, Or.inl he⟩⟩
  loopless := ⟨fun a h => (U.localEdge_adj h).ne rfl⟩

/-- Cycles in translates of the local orbit graph. Zero walks are harmless. -/
def baseCycles : SimpleGraph.WalkClosure.Cycles U.graph := fun _ p =>
  ∃ g : G, SimpleGraph.WalkClosure.Supported
    (fun a b => U.localEdge (g⁻¹ • a) (g⁻¹ • b)) p

/-- The source base condition: translated local cycles generate all cycles. -/
def IsBase : Prop := SimpleGraph.WalkClosure.IsCycleBase U.baseCycles

/-- Condition (U) forces the local group to contain an edge reversal. -/
theorem exists_swap : ∃ t : U.H, (t : G) • U.x = U.y ∧ (t : G) • U.y = U.x := by
  classical
  by_contra h
  have hle : U.H ⊓ U.edgeSetGroup ≤ U.vertexGroup := by
    intro g hg
    rcases hg.2 with hf | hs
    · exact hf.1
    · exact False.elim (h ⟨⟨g, hg.1⟩, hs⟩)
  have hH : U.H ≤ U.vertexGroup := by
    rw [← U.local_generate]
    exact sup_le hle inf_le_right
  obtain ⟨g, hg⟩ := U.local_orbit
  exact U.adjacent.ne ((hH g.property).symm.trans hg)

/-- Edge reversals preserve the pointwise edge stabilizer under conjugation. -/
theorem conj_mem_edgeGroup {t : G} (htx : t • U.x = U.y) (hty : t • U.y = U.x)
    {b : G} (hb : b ∈ U.edgeGroup) : t * b * t⁻¹ ∈ U.edgeGroup := by
  have htx' : t⁻¹ • U.x = U.y := by rw [inv_smul_eq_iff, hty]
  have hty' : t⁻¹ • U.y = U.x := by rw [inv_smul_eq_iff, htx]
  exact ⟨by change (t * b * t⁻¹) • U.x = U.x
            rw [mul_smul, mul_smul, htx', show b • U.y = U.y from hb.2, hty],
         by change (t * b * t⁻¹) • U.y = U.y
            rw [mul_smul, mul_smul, hty', show b • U.x = U.x from hb.1, htx]⟩

end System

variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

/-- Compatible local isomorphisms, as on p.199 of *Sporadic Groups*. -/
structure Similarity (U : System G V) (U' : System G' V') where
  vertexIso : U.vertexGroup ≃* U'.vertexGroup
  localIso : U.H ≃* U'.H
  agree : ∀ (g : G) (hgH : g ∈ U.H) (hgx : g ∈ U.vertexGroup),
    (vertexIso ⟨g, hgx⟩ : G') = (localIso ⟨g, hgH⟩ : G')
  local_vertex : ∀ h : U.H, (h : G) ∈ U.vertexGroup ↔
    (localIso h : G') ∈ U'.vertexGroup
  edge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
    (vertexIso a : G') ∈ U'.edgeGroup
  local_edge : ∀ h : U.H, (h : G) ∈ U.edgeSetGroup ↔
    (localIso h : G') ∈ U'.edgeSetGroup

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- Equivalence is the additional edge-conjugation identity, not global recognition. -/
def IsEquivalence : Prop :=
  ∃ (t : U.H) (htx : (t : G) • U.x = U.y) (hty : (t : G) • U.y = U.x),
    ∀ b : U.edgeGroup,
      (s.vertexIso ⟨(t : G) * (b : G) * (t : G)⁻¹,
        (U.conj_mem_edgeGroup htx hty b.property).1⟩ : G') =
      (s.localIso t : G') * (s.vertexIso ⟨b, b.property.1⟩ : G') * (s.localIso t : G')⁻¹

/-- A similarity carries a local edge reversal to a local edge reversal. -/
theorem map_swap (t : U.H) (htx : (t : G) • U.x = U.y)
    (hty : (t : G) • U.y = U.x) :
    (s.localIso t : G') • U'.x = U'.y ∧ (s.localIso t : G') • U'.y = U'.x := by
  have hm := (s.local_edge t).mp (Or.inr ⟨htx, hty⟩)
  rcases hm with hf | hs
  · have ht : (t : G) ∈ U.vertexGroup := (s.local_vertex t).mpr hf.1
    exact False.elim (U.adjacent.ne (ht.symm.trans htx))
  · exact hs

end Similarity

end Theory.GroupTheory.GraphUniquenessSystem
